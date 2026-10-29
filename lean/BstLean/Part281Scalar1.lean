import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 11884 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11884. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11884 : WorldParameters where
  hiddenCharge := (1211856821 / 1000000000000 : ℝ)
  frame := (637717784377 / 1000000000000 : ℝ)
  moment := (2802547517 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11884 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737471272377 / 500000000000 : ℝ)
    root := (364280929 / 50000000000 : ℝ) }

noncomputable def scalar11884 : ScalarCertificate 11884 world11884 agent11884 where
  dimensionLo := 11884
  dimensionHi := 11884
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2382811699 / 1000000000000 : ℝ)
  frameLo := (637717784377 / 1000000000000 : ℝ)
  frameHi := (737471272377 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11884]
  agentFrame_pos := by norm_num only [agent11884]
  worldRadius := (2382811699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11884]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1303160227 / 1000000000000 : ℝ)
  lowerTail := (831357597 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1590280933 / 200000000000 : ℝ)
  ledger := by
    have h : (1211856821 / 1000000000000 : ℚ) +
        (2802547517 / 250000000000000000 : ℚ) / (2382811699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1303160227 / 1000000000000 : ℚ) + (831357597 / 500000000000 : ℚ) ≤
        (1590280933 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1211856821 / 1000000000000 : ℚ) +
        (2802547517 / 250000000000000000 : ℚ) / (2382811699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1303160227 / 1000000000000 : ℚ) + (831357597 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1590280933 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11884]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11884 :
    2 * 160 < 11884 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995599 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11884 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11885 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11885. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11885 : WorldParameters where
  hiddenCharge := (1211802297 / 1000000000000 : ℝ)
  frame := (637701920849 / 1000000000000 : ℝ)
  moment := (5603859059 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11885 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (184362023379 / 125000000000 : ℝ)
    root := (58279479 / 8000000000 : ℝ) }

noncomputable def scalar11885 : ScalarCertificate 11885 world11885 agent11885 where
  dimensionLo := 11885
  dimensionHi := 11885
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2383225799 / 1000000000000 : ℝ)
  frameLo := (637701920849 / 1000000000000 : ℝ)
  frameHi := (184362023379 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11885]
  agentFrame_pos := by norm_num only [agent11885]
  worldRadius := (2383225799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11885]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (260395877 / 200000000000 : ℝ)
  lowerTail := (830660493 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7947653729 / 1000000000000 : ℝ)
  ledger := by
    have h : (1211802297 / 1000000000000 : ℚ) +
        (5603859059 / 500000000000000000 : ℚ) / (2383225799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (260395877 / 200000000000 : ℚ) + (830660493 / 500000000000 : ℚ) ≤
        (7947653729 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1211802297 / 1000000000000 : ℚ) +
        (5603859059 / 500000000000000000 : ℚ) / (2383225799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (260395877 / 200000000000 : ℚ) + (830660493 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7947653729 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11885]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11885 :
    2 * 160 < 11885 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999181 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11885 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11886 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11886. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11886 : WorldParameters where
  hiddenCharge := (1211747789 / 1000000000000 : ℝ)
  frame := (637686060081 / 1000000000000 : ℝ)
  moment := (11205246929 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11886 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368712465073 / 250000000000 : ℝ)
    root := (3642125747 / 500000000000 : ℝ) }

noncomputable def scalar11886 : ScalarCertificate 11886 world11886 agent11886 where
  dimensionLo := 11886
  dimensionHi := 11886
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2383639999 / 1000000000000 : ℝ)
  frameLo := (637686060081 / 1000000000000 : ℝ)
  frameHi := (368712465073 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11886]
  agentFrame_pos := by norm_num only [agent11886]
  worldRadius := (2383639999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11886]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (260159993 / 200000000000 : ℝ)
  lowerTail := (414982091 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7943906443 / 1000000000000 : ℝ)
  ledger := by
    have h : (1211747789 / 1000000000000 : ℚ) +
        (11205246929 / 1000000000000000000 : ℚ) / (2383639999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (260159993 / 200000000000 : ℚ) + (414982091 / 250000000000 : ℚ) ≤
        (7943906443 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1211747789 / 1000000000000 : ℚ) +
        (11205246929 / 1000000000000000000 : ℚ) / (2383639999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (260159993 / 200000000000 : ℚ) + (414982091 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7943906443 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11886]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11886 :
    2 * 160 < 11886 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997009 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11886 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11887 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11887. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11887 : WorldParameters where
  hiddenCharge := (75730831 / 62500000000 : ℝ)
  frame := (637670202073 / 1000000000000 : ℝ)
  moment := (5601388251 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11887 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474803558547 / 1000000000000 : ℝ)
    root := (7283568277 / 1000000000000 : ℝ) }

noncomputable def scalar11887 : ScalarCertificate 11887 world11887 agent11887 where
  dimensionLo := 11887
  dimensionHi := 11887
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2384054199 / 1000000000000 : ℝ)
  frameLo := (637670202073 / 1000000000000 : ℝ)
  frameHi := (1474803558547 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11887]
  agentFrame_pos := by norm_num only [agent11887]
  worldRadius := (2384054199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11887]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1299621743 / 1000000000000 : ℝ)
  lowerTail := (66341483 / 40000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3970081249 / 500000000000 : ℝ)
  ledger := by
    have h : (75730831 / 62500000000 : ℚ) +
        (5601388251 / 500000000000000000 : ℚ) / (2384054199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1299621743 / 1000000000000 : ℚ) + (66341483 / 40000000000 : ℚ) ≤
        (3970081249 / 500000000000 : ℚ) := by norm_num only
    have hc : (((75730831 / 62500000000 : ℚ) +
        (5601388251 / 500000000000000000 : ℚ) / (2384054199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1299621743 / 1000000000000 : ℚ) + (66341483 / 40000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3970081249 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11887]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11887 :
    2 * 160 < 11887 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997441 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11887 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11888 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11888. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11888 : WorldParameters where
  hiddenCharge := (605819409 / 500000000000 : ℝ)
  frame := (318827173411 / 500000000000 : ℝ)
  moment := (2240061367 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11888 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147475727581 / 100000000000 : ℝ)
    root := (910360673 / 125000000000 : ℝ) }

noncomputable def scalar11888 : ScalarCertificate 11888 world11888 agent11888 where
  dimensionLo := 11888
  dimensionHi := 11888
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2384468199 / 1000000000000 : ℝ)
  frameLo := (318827173411 / 500000000000 : ℝ)
  frameHi := (147475727581 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11888]
  agentFrame_pos := by norm_num only [agent11888]
  worldRadius := (2384468199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11888]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1298444663 / 1000000000000 : ℝ)
  lowerTail := (1657147037 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1984105521 / 250000000000 : ℝ)
  ledger := by
    have h : (605819409 / 500000000000 : ℚ) +
        (2240061367 / 200000000000000000 : ℚ) / (2384468199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1298444663 / 1000000000000 : ℚ) + (1657147037 / 1000000000000 : ℚ) ≤
        (1984105521 / 250000000000 : ℚ) := by norm_num only
    have hc : (((605819409 / 500000000000 : ℚ) +
        (2240061367 / 200000000000000000 : ℚ) / (2384468199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1298444663 / 1000000000000 : ℚ) + (1657147037 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1984105521 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11888]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11888 :
    2 * 160 < 11888 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998603 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11888 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11889 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11889. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11889 : WorldParameters where
  hiddenCharge := (302896089 / 250000000000 : ℝ)
  frame := (79704811791 / 125000000000 : ℝ)
  moment := (1399729741 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11889 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147471102401 / 100000000000 : ℝ)
    root := (1456440531 / 200000000000 : ℝ) }

noncomputable def scalar11889 : ScalarCertificate 11889 world11889 agent11889 where
  dimensionLo := 11889
  dimensionHi := 11889
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2384882399 / 1000000000000 : ℝ)
  frameLo := (79704811791 / 125000000000 : ℝ)
  frameHi := (147471102401 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11889]
  agentFrame_pos := by norm_num only [agent11889]
  worldRadius := (2384882399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11889]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (648634477 / 500000000000 : ℝ)
  lowerTail := (1655758539 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7932685059 / 1000000000000 : ℝ)
  ledger := by
    have h : (302896089 / 250000000000 : ℚ) +
        (1399729741 / 125000000000000000 : ℚ) / (2384882399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (648634477 / 500000000000 : ℚ) + (1655758539 / 1000000000000 : ℚ) ≤
        (7932685059 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((302896089 / 250000000000 : ℚ) +
        (1399729741 / 125000000000000000 : ℚ) / (2384882399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (648634477 / 500000000000 : ℚ) + (1655758539 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7932685059 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11889]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11889 :
    2 * 160 < 11889 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996469 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11889 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11890 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11890. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11890 : WorldParameters where
  hiddenCharge := (121152991 / 100000000000 : ℝ)
  frame := (39851415287 / 62500000000 : ℝ)
  moment := (5597684891 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11890 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474664797161 / 1000000000000 : ℝ)
    root := (910190031 / 125000000000 : ℝ) }

noncomputable def scalar11890 : ScalarCertificate 11890 world11890 agent11890 where
  dimensionLo := 11890
  dimensionHi := 11890
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2385296499 / 1000000000000 : ℝ)
  frameLo := (39851415287 / 62500000000 : ℝ)
  frameHi := (1474664797161 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11890]
  agentFrame_pos := by norm_num only [agent11890]
  worldRadius := (2385296499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11890]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (324023621 / 250000000000 : ℝ)
  lowerTail := (1654371409 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1982237903 / 250000000000 : ℝ)
  ledger := by
    have h : (121152991 / 100000000000 : ℚ) +
        (5597684891 / 500000000000000000 : ℚ) / (2385296499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (324023621 / 250000000000 : ℚ) + (1654371409 / 1000000000000 : ℚ) ≤
        (1982237903 / 250000000000 : ℚ) := by norm_num only
    have hc : (((121152991 / 100000000000 : ℚ) +
        (5597684891 / 500000000000000000 : ℚ) / (2385296499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (324023621 / 250000000000 : ℚ) + (1654371409 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1982237903 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11890]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11890 :
    2 * 160 < 11890 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749998571 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11890 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11891 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11891. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11891 : WorldParameters where
  hiddenCharge := (1211475479 / 1000000000000 : ℝ)
  frame := (637606797611 / 1000000000000 : ℝ)
  moment := (2798225599 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11891 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368654647319 / 250000000000 : ℝ)
    root := (1456167601 / 200000000000 : ℝ) }

noncomputable def scalar11891 : ScalarCertificate 11891 world11891 agent11891 where
  dimensionLo := 11891
  dimensionHi := 11891
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2385710699 / 1000000000000 : ℝ)
  frameLo := (637606797611 / 1000000000000 : ℝ)
  frameHi := (368654647319 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11891]
  agentFrame_pos := by norm_num only [agent11891]
  worldRadius := (2385710699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11891]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (647460629 / 500000000000 : ℝ)
  lowerTail := (1652985663 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1585044287 / 200000000000 : ℝ)
  ledger := by
    have h : (1211475479 / 1000000000000 : ℚ) +
        (2798225599 / 250000000000000000 : ℚ) / (2385710699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (647460629 / 500000000000 : ℚ) + (1652985663 / 1000000000000 : ℚ) ≤
        (1585044287 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1211475479 / 1000000000000 : ℚ) +
        (2798225599 / 250000000000000000 : ℚ) / (2385710699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (647460629 / 500000000000 : ℚ) + (1652985663 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1585044287 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11891]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11891 :
    2 * 160 < 11891 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997859 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11891 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11892 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11892. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11892 : WorldParameters where
  hiddenCharge := (1211421063 / 1000000000000 : ℝ)
  frame := (127518190677 / 200000000000 : ℝ)
  moment := (11190435769 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11892 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474572412283 / 1000000000000 : ℝ)
    root := (1456031217 / 200000000000 : ℝ) }

noncomputable def scalar11892 : ScalarCertificate 11892 world11892 agent11892 where
  dimensionLo := 11892
  dimensionHi := 11892
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2386124799 / 1000000000000 : ℝ)
  frameLo := (127518190677 / 200000000000 : ℝ)
  frameHi := (1474572412283 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11892]
  agentFrame_pos := by norm_num only [agent11892]
  worldRadius := (2386124799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11892]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (323437323 / 250000000000 : ℝ)
  lowerTail := (825800657 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1980373721 / 250000000000 : ℝ)
  ledger := by
    have h : (1211421063 / 1000000000000 : ℚ) +
        (11190435769 / 1000000000000000000 : ℚ) / (2386124799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (323437323 / 250000000000 : ℚ) + (825800657 / 500000000000 : ℚ) ≤
        (1980373721 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1211421063 / 1000000000000 : ℚ) +
        (11190435769 / 1000000000000000000 : ℚ) / (2386124799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (323437323 / 250000000000 : ℚ) + (825800657 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1980373721 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11892]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11892 :
    2 * 160 < 11892 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997739 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11892 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11893 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11893. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11893 : WorldParameters where
  hiddenCharge := (605683331 / 500000000000 : ℝ)
  frame := (637575111913 / 1000000000000 : ℝ)
  moment := (5593984951 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11893 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737263127113 / 500000000000 : ℝ)
    root := (909934291 / 125000000000 : ℝ) }

noncomputable def scalar11893 : ScalarCertificate 11893 world11893 agent11893 where
  dimensionLo := 11893
  dimensionHi := 11893
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2386538999 / 1000000000000 : ℝ)
  frameLo := (637575111913 / 1000000000000 : ℝ)
  frameHi := (737263127113 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11893]
  agentFrame_pos := by norm_num only [agent11893]
  worldRadius := (2386538999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11893]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1292578567 / 1000000000000 : ℝ)
  lowerTail := (330043669 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1583554319 / 200000000000 : ℝ)
  ledger := by
    have h : (605683331 / 500000000000 : ℚ) +
        (5593984951 / 500000000000000000 : ℚ) / (2386538999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1292578567 / 1000000000000 : ℚ) + (330043669 / 200000000000 : ℚ) ≤
        (1583554319 / 200000000000 : ℚ) := by norm_num only
    have hc : (((605683331 / 500000000000 : ℚ) +
        (5593984951 / 500000000000000000 : ℚ) / (2386538999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1292578567 / 1000000000000 : ℚ) + (330043669 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1583554319 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11893]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11893 :
    2 * 160 < 11893 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998799 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11893 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11894 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11894. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11894 : WorldParameters where
  hiddenCharge := (1211312277 / 1000000000000 : ℝ)
  frame := (159389818299 / 250000000000 : ℝ)
  moment := (5592752397 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11894 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474480127031 / 1000000000000 : ℝ)
    root := (3639396407 / 500000000000 : ℝ) }

noncomputable def scalar11894 : ScalarCertificate 11894 world11894 agent11894 where
  dimensionLo := 11894
  dimensionHi := 11894
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2386953099 / 1000000000000 : ℝ)
  frameLo := (159389818299 / 250000000000 : ℝ)
  frameHi := (1474480127031 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11894]
  agentFrame_pos := by norm_num only [agent11894]
  worldRadius := (2386953099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11894]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (645704519 / 500000000000 : ℝ)
  lowerTail := (824418353 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7914051801 / 1000000000000 : ℝ)
  ledger := by
    have h : (1211312277 / 1000000000000 : ℚ) +
        (5592752397 / 500000000000000000 : ℚ) / (2386953099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (645704519 / 500000000000 : ℚ) + (824418353 / 500000000000 : ℚ) ≤
        (7914051801 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1211312277 / 1000000000000 : ℚ) +
        (5592752397 / 500000000000000000 : ℚ) / (2386953099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (645704519 / 500000000000 : ℚ) + (824418353 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7914051801 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11894]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11894 :
    2 * 160 < 11894 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996097 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11894 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11895 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11895. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11895 : WorldParameters where
  hiddenCharge := (302814477 / 250000000000 : ℝ)
  frame := (63754343723 / 100000000000 : ℝ)
  moment := (2795760111 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11895 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737217009371 / 500000000000 : ℝ)
    root := (3639055811 / 500000000000 : ℝ) }

noncomputable def scalar11895 : ScalarCertificate 11895 world11895 agent11895 where
  dimensionLo := 11895
  dimensionHi := 11895
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2387367099 / 1000000000000 : ℝ)
  frameLo := (63754343723 / 100000000000 : ℝ)
  frameHi := (737217009371 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11895]
  agentFrame_pos := by norm_num only [agent11895]
  worldRadius := (2387367099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11895]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1290240717 / 1000000000000 : ℝ)
  lowerTail := (329491279 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (791033551 / 100000000000 : ℝ)
  ledger := by
    have h : (302814477 / 250000000000 : ℚ) +
        (2795760111 / 250000000000000000 : ℚ) / (2387367099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1290240717 / 1000000000000 : ℚ) + (329491279 / 200000000000 : ℚ) ≤
        (791033551 / 100000000000 : ℚ) := by norm_num only
    have hc : (((302814477 / 250000000000 : ℚ) +
        (2795760111 / 250000000000000000 : ℚ) / (2387367099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1290240717 / 1000000000000 : ℚ) + (329491279 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((791033551 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11895]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11895 :
    2 * 160 < 11895 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999039 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11895 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11896 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11896. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11896 : WorldParameters where
  hiddenCharge := (605601777 / 500000000000 : ℝ)
  frame := (637527604017 / 1000000000000 : ℝ)
  moment := (11180576853 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11896 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (294877588257 / 200000000000 : ℝ)
    root := (113709853 / 15625000000 : ℝ) }

noncomputable def scalar11896 : ScalarCertificate 11896 world11896 agent11896 where
  dimensionLo := 11896
  dimensionHi := 11896
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2387781299 / 1000000000000 : ℝ)
  frameLo := (637527604017 / 1000000000000 : ℝ)
  frameHi := (294877588257 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11896]
  agentFrame_pos := by norm_num only [agent11896]
  worldRadius := (2387781299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11896]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (257814751 / 200000000000 : ℝ)
  lowerTail := (411519403 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3953311291 / 500000000000 : ℝ)
  ledger := by
    have h : (605601777 / 500000000000 : ℚ) +
        (11180576853 / 1000000000000000000 : ℚ) / (2387781299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (257814751 / 200000000000 : ℚ) + (411519403 / 250000000000 : ℚ) ≤
        (3953311291 / 500000000000 : ℚ) := by norm_num only
    have hc : (((605601777 / 500000000000 : ℚ) +
        (11180576853 / 1000000000000000000 : ℚ) / (2387781299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (257814751 / 200000000000 : ℚ) + (411519403 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3953311291 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11896]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11896 :
    2 * 160 < 11896 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995891 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11896 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11897 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11897. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11897 : WorldParameters where
  hiddenCharge := (242229843 / 200000000000 : ℝ)
  frame := (159377943389 / 250000000000 : ℝ)
  moment := (558905701 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11897 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737170941353 / 500000000000 : ℝ)
    root := (1455349977 / 200000000000 : ℝ) }

noncomputable def scalar11897 : ScalarCertificate 11897 world11897 agent11897 where
  dimensionLo := 11897
  dimensionHi := 11897
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2388195399 / 1000000000000 : ℝ)
  frameLo := (159377943389 / 250000000000 : ℝ)
  frameHi := (737170941353 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11897]
  agentFrame_pos := by norm_num only [agent11897]
  worldRadius := (2388195399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11897]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (643953999 / 500000000000 : ℝ)
  lowerTail := (328940031 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7902913149 / 1000000000000 : ℝ)
  ledger := by
    have h : (242229843 / 200000000000 : ℚ) +
        (558905701 / 50000000000000000 : ℚ) / (2388195399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (643953999 / 500000000000 : ℚ) + (328940031 / 200000000000 : ℚ) ≤
        (7902913149 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((242229843 / 200000000000 : ℚ) +
        (558905701 / 50000000000000000 : ℚ) / (2388195399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (643953999 / 500000000000 : ℚ) + (328940031 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7902913149 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11897]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11897 :
    2 * 160 < 11897 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999791 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11897 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11898 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11898. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11898 : WorldParameters where
  hiddenCharge := (302773723 / 250000000000 : ℝ)
  frame := (159373986461 / 250000000000 : ℝ)
  moment := (1396956493 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11898 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474295854929 / 1000000000000 : ℝ)
    root := (7276069339 / 1000000000000 : ℝ) }

noncomputable def scalar11898 : ScalarCertificate 11898 world11898 agent11898 where
  dimensionLo := 11898
  dimensionHi := 11898
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2388609499 / 1000000000000 : ℝ)
  frameLo := (159373986461 / 250000000000 : ℝ)
  frameHi := (1474295854929 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11898]
  agentFrame_pos := by norm_num only [agent11898]
  worldRadius := (2388609499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11898]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (643371723 / 500000000000 : ℝ)
  lowerTail := (328664809 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (789920707 / 100000000000 : ℝ)
  ledger := by
    have h : (302773723 / 250000000000 : ℚ) +
        (1396956493 / 125000000000000000 : ℚ) / (2388609499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (643371723 / 500000000000 : ℚ) + (328664809 / 200000000000 : ℚ) ≤
        (789920707 / 100000000000 : ℚ) := by norm_num only
    have hc : (((302773723 / 250000000000 : ℚ) +
        (1396956493 / 125000000000000000 : ℚ) / (2388609499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (643371723 / 500000000000 : ℚ) + (328664809 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((789920707 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11898]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11898 :
    2 * 160 < 11898 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994609 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11898 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11899 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11899. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11899 : WorldParameters where
  hiddenCharge := (151380073 / 125000000000 : ℝ)
  frame := (637480120883 / 1000000000000 : ℝ)
  moment := (11173190627 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11899 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737124923001 / 500000000000 : ℝ)
    root := (1818847259 / 250000000000 : ℝ) }

noncomputable def scalar11899 : ScalarCertificate 11899 world11899 agent11899 where
  dimensionLo := 11899
  dimensionHi := 11899
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2389023599 / 1000000000000 : ℝ)
  frameLo := (637480120883 / 1000000000000 : ℝ)
  frameHi := (737124923001 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11899]
  agentFrame_pos := by norm_num only [agent11899]
  worldRadius := (2389023599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11899]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1285580111 / 1000000000000 : ℝ)
  lowerTail := (820974641 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1579100871 / 200000000000 : ℝ)
  ledger := by
    have h : (151380073 / 125000000000 : ℚ) +
        (11173190627 / 1000000000000000000 : ℚ) / (2389023599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1285580111 / 1000000000000 : ℚ) + (820974641 / 500000000000 : ℚ) ≤
        (1579100871 / 200000000000 : ℚ) := by norm_num only
    have hc : (((151380073 / 125000000000 : ℚ) +
        (11173190627 / 1000000000000000000 : ℚ) / (2389023599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1285580111 / 1000000000000 : ℚ) + (820974641 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1579100871 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11899]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11899 :
    2 * 160 < 11899 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996419 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11899 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11900 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11900. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11900 : WorldParameters where
  hiddenCharge := (1210986291 / 1000000000000 : ℝ)
  frame := (63746429867 / 100000000000 : ℝ)
  moment := (5585365033 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11900 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474203861877 / 1000000000000 : ℝ)
    root := (3637354527 / 500000000000 : ℝ) }

noncomputable def scalar11900 : ScalarCertificate 11900 world11900 agent11900 where
  dimensionLo := 11900
  dimensionHi := 11900
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2389437799 / 1000000000000 : ℝ)
  frameLo := (63746429867 / 100000000000 : ℝ)
  frameHi := (1474203861877 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11900]
  agentFrame_pos := by norm_num only [agent11900]
  worldRadius := (2389437799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11900]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (25688363 / 20000000000 : ℝ)
  lowerTail := (1640576047 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (394590259 / 50000000000 : ℝ)
  ledger := by
    have h : (1210986291 / 1000000000000 : ℚ) +
        (5585365033 / 500000000000000000 : ℚ) / (2389437799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (25688363 / 20000000000 : ℚ) + (1640576047 / 1000000000000 : ℚ) ≤
        (394590259 / 50000000000 : ℚ) := by norm_num only
    have hc : (((1210986291 / 1000000000000 : ℚ) +
        (5585365033 / 500000000000000000 : ℚ) / (2389437799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (25688363 / 20000000000 : ℚ) + (1640576047 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((394590259 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11900]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11900 :
    2 * 160 < 11900 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997869 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11900 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11901 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11901. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11901 : WorldParameters where
  hiddenCharge := (605466007 / 500000000000 : ℝ)
  frame := (318724239603 / 500000000000 : ℝ)
  moment := (5584135131 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11901 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737078951271 / 500000000000 : ℝ)
    root := (3637014617 / 500000000000 : ℝ) }

noncomputable def scalar11901 : ScalarCertificate 11901 world11901 agent11901 where
  dimensionLo := 11901
  dimensionHi := 11901
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2389851899 / 1000000000000 : ℝ)
  frameLo := (318724239603 / 500000000000 : ℝ)
  frameHi := (737078951271 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11901]
  agentFrame_pos := by norm_num only [agent11901]
  worldRadius := (2389851899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11901]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (320814323 / 250000000000 : ℝ)
  lowerTail := (409801009 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7888109293 / 1000000000000 : ℝ)
  ledger := by
    have h : (605466007 / 500000000000 : ℚ) +
        (5584135131 / 500000000000000000 : ℚ) / (2389851899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (320814323 / 250000000000 : ℚ) + (409801009 / 250000000000 : ℚ) ≤
        (7888109293 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((605466007 / 500000000000 : ℚ) +
        (5584135131 / 500000000000000000 : ℚ) / (2389851899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (320814323 / 250000000000 : ℚ) + (409801009 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7888109293 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11901]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11901 :
    2 * 160 < 11901 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998929 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11901 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11902 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11902. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11902 : WorldParameters where
  hiddenCharge := (151359719 / 125000000000 : ℝ)
  frame := (637432662489 / 1000000000000 : ℝ)
  moment := (2233162243 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11902 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737055983991 / 500000000000 : ℝ)
    root := (1454669931 / 200000000000 : ℝ) }

noncomputable def scalar11902 : ScalarCertificate 11902 world11902 agent11902 where
  dimensionLo := 11902
  dimensionHi := 11902
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2390265999 / 1000000000000 : ℝ)
  frameLo := (637432662489 / 1000000000000 : ℝ)
  frameHi := (737055983991 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11902]
  agentFrame_pos := by norm_num only [agent11902]
  worldRadius := (2390265999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11902]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1282097669 / 1000000000000 : ℝ)
  lowerTail := (818916699 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3942208407 / 500000000000 : ℝ)
  ledger := by
    have h : (151359719 / 125000000000 : ℚ) +
        (2233162243 / 200000000000000000 : ℚ) / (2390265999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1282097669 / 1000000000000 : ℚ) + (818916699 / 500000000000 : ℚ) ≤
        (3942208407 / 500000000000 : ℚ) := by norm_num only
    have hc : (((151359719 / 125000000000 : ℚ) +
        (2233162243 / 200000000000000000 : ℚ) / (2390265999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1282097669 / 1000000000000 : ℚ) + (818916699 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3942208407 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11902]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11902 :
    2 * 160 < 11902 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (687499973 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11902 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11903 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11903. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11903 : WorldParameters where
  hiddenCharge := (605411753 / 500000000000 : ℝ)
  frame := (637416848519 / 1000000000000 : ℝ)
  moment := (446534117 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11903 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474066058181 / 1000000000000 : ℝ)
    root := (7272670397 / 1000000000000 : ℝ) }

noncomputable def scalar11903 : ScalarCertificate 11903 world11903 agent11903 where
  dimensionLo := 11903
  dimensionHi := 11903
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2390680099 / 1000000000000 : ℝ)
  frameLo := (637416848519 / 1000000000000 : ℝ)
  frameHi := (1474066058181 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11903]
  agentFrame_pos := by norm_num only [agent11903]
  worldRadius := (2390680099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11903]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (64046967 / 50000000000 : ℝ)
  lowerTail := (327292839 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3940363931 / 500000000000 : ℝ)
  ledger := by
    have h : (605411753 / 500000000000 : ℚ) +
        (446534117 / 40000000000000000 : ℚ) / (2390680099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (64046967 / 50000000000 : ℚ) + (327292839 / 200000000000 : ℚ) ≤
        (3940363931 / 500000000000 : ℚ) := by norm_num only
    have hc : (((605411753 / 500000000000 : ℚ) +
        (446534117 / 40000000000000000 : ℚ) / (2390680099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (64046967 / 50000000000 : ℚ) + (327292839 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3940363931 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11903]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11903 :
    2 * 160 < 11903 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999939 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11903 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11904 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11904. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11904 : WorldParameters where
  hiddenCharge := (48430771 / 40000000000 : ℝ)
  frame := (127480207459 / 200000000000 : ℝ)
  moment := (1116089539 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11904 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737010086563 / 500000000000 : ℝ)
    root := (7271991301 / 1000000000000 : ℝ) }

noncomputable def scalar11904 : ScalarCertificate 11904 world11904 agent11904 where
  dimensionLo := 11904
  dimensionHi := 11904
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2391094299 / 1000000000000 : ℝ)
  frameLo := (127480207459 / 200000000000 : ℝ)
  frameHi := (737010086563 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11904]
  agentFrame_pos := by norm_num only [agent11904]
  worldRadius := (2391094299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11904]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1279782259 / 1000000000000 : ℝ)
  lowerTail := (1635096387 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7877042187 / 1000000000000 : ℝ)
  ledger := by
    have h : (48430771 / 40000000000 : ℚ) +
        (1116089539 / 100000000000000000 : ℚ) / (2391094299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1279782259 / 1000000000000 : ℚ) + (1635096387 / 1000000000000 : ℚ) ≤
        (7877042187 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((48430771 / 40000000000 : ℚ) +
        (1116089539 / 100000000000000000 : ℚ) / (2391094299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1279782259 / 1000000000000 : ℚ) + (1635096387 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7877042187 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11904]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11904 :
    2 * 160 < 11904 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999461 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11904 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11905 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11905. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11905 : WorldParameters where
  hiddenCharge := (1210715059 / 1000000000000 : ℝ)
  frame := (39836576801 / 62500000000 : ℝ)
  moment := (11158438611 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11905 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473974312801 / 1000000000000 : ℝ)
    root := (290852501 / 40000000000 : ℝ) }

noncomputable def scalar11905 : ScalarCertificate 11905 world11905 agent11905 where
  dimensionLo := 11905
  dimensionHi := 11905
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2391508399 / 1000000000000 : ℝ)
  frameLo := (39836576801 / 62500000000 : ℝ)
  frameHi := (1473974312801 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11905]
  agentFrame_pos := by norm_num only [agent11905]
  worldRadius := (2391508399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11905]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (639313197 / 500000000000 : ℝ)
  lowerTail := (408432481 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (246042501 / 31250000000 : ℝ)
  ledger := by
    have h : (1210715059 / 1000000000000 : ℚ) +
        (11158438611 / 1000000000000000000 : ℚ) / (2391508399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (639313197 / 500000000000 : ℚ) + (408432481 / 250000000000 : ℚ) ≤
        (246042501 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1210715059 / 1000000000000 : ℚ) +
        (11158438611 / 1000000000000000000 : ℚ) / (2391508399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (639313197 / 500000000000 : ℚ) + (408432481 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((246042501 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11905]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11905 :
    2 * 160 < 11905 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999327 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11905 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11906 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11906. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11906 : WorldParameters where
  hiddenCharge := (605330429 / 500000000000 : ℝ)
  frame := (318684711541 / 500000000000 : ℝ)
  moment := (11155982587 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11906 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473928477193 / 1000000000000 : ℝ)
    root := (7270633909 / 1000000000000 : ℝ) }

noncomputable def scalar11906 : ScalarCertificate 11906 world11906 agent11906 where
  dimensionLo := 11906
  dimensionHi := 11906
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2391922499 / 1000000000000 : ℝ)
  frameLo := (318684711541 / 500000000000 : ℝ)
  frameHi := (1473928477193 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11906]
  agentFrame_pos := by norm_num only [agent11906]
  worldRadius := (2391922499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11906]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1277471699 / 1000000000000 : ℝ)
  lowerTail := (1632364763 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3934840573 / 500000000000 : ℝ)
  ledger := by
    have h : (605330429 / 500000000000 : ℚ) +
        (11155982587 / 1000000000000000000 : ℚ) / (2391922499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1277471699 / 1000000000000 : ℚ) + (1632364763 / 1000000000000 : ℚ) ≤
        (3934840573 / 500000000000 : ℚ) := by norm_num only
    have hc : (((605330429 / 500000000000 : ℚ) +
        (11155982587 / 1000000000000000000 : ℚ) / (2391922499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1277471699 / 1000000000000 : ℚ) + (1632364763 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3934840573 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11906]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11906 :
    2 * 160 < 11906 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999461 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11906 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11907 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11907. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11907 : WorldParameters where
  hiddenCharge := (1210606673 / 1000000000000 : ℝ)
  frame := (637353620091 / 1000000000000 : ℝ)
  moment := (11153527319 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11907 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736941333143 / 500000000000 : ℝ)
    root := (1453991107 / 200000000000 : ℝ) }

noncomputable def scalar11907 : ScalarCertificate 11907 world11907 agent11907 where
  dimensionLo := 11907
  dimensionHi := 11907
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2392336499 / 1000000000000 : ℝ)
  frameLo := (637353620091 / 1000000000000 : ℝ)
  frameHi := (736941333143 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11907]
  agentFrame_pos := by norm_num only [agent11907]
  worldRadius := (2392336499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11907]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (638159079 / 500000000000 : ℝ)
  lowerTail := (20387511 / 12500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (157320113 / 20000000000 : ℝ)
  ledger := by
    have h : (1210606673 / 1000000000000 : ℚ) +
        (11153527319 / 1000000000000000000 : ℚ) / (2392336499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (638159079 / 500000000000 : ℚ) + (20387511 / 12500000000 : ℚ) ≤
        (157320113 / 20000000000 : ℚ) := by norm_num only
    have hc : (((1210606673 / 1000000000000 : ℚ) +
        (11153527319 / 1000000000000000000 : ℚ) / (2392336499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (638159079 / 500000000000 : ℚ) + (20387511 / 12500000000 : ℚ) : ℚ) : ℝ) ≤
        ((157320113 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11907]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11907 :
    2 * 160 < 11907 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997691 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11907 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11908 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11908. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11908 : WorldParameters where
  hiddenCharge := (151319063 / 125000000000 : ℝ)
  frame := (637337819843 / 1000000000000 : ℝ)
  moment := (2230214561 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11908 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473836874101 / 1000000000000 : ℝ)
    root := (7269277401 / 1000000000000 : ℝ) }

noncomputable def scalar11908 : ScalarCertificate 11908 world11908 agent11908 where
  dimensionLo := 11908
  dimensionHi := 11908
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2392750699 / 1000000000000 : ℝ)
  frameLo := (637337819843 / 1000000000000 : ℝ)
  frameHi := (1473836874101 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11908]
  agentFrame_pos := by norm_num only [agent11908]
  worldRadius := (2392750699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11908]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1275165969 / 1000000000000 : ℝ)
  lowerTail := (814819253 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7862333483 / 1000000000000 : ℝ)
  ledger := by
    have h : (151319063 / 125000000000 : ℚ) +
        (2230214561 / 200000000000000000 : ℚ) / (2392750699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1275165969 / 1000000000000 : ℚ) + (814819253 / 500000000000 : ℚ) ≤
        (7862333483 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((151319063 / 125000000000 : ℚ) +
        (2230214561 / 200000000000000000 : ℚ) / (2392750699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1275165969 / 1000000000000 : ℚ) + (814819253 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7862333483 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11908]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11908 :
    2 * 160 < 11908 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999747 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11908 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding11884 :
    (1211856820803637639097 / 1000000000000000000000000 : ℝ) ≤ world11884.hiddenCharge ∧
    (637717784376268454190663 / 1000000000000000000000000 : ℝ) ≤ world11884.frame ∧
    (2802547517 / 250000000000000000 : ℝ) ≤ world11884.moment ∧
    (1474942544753485553567857 / 1000000000000000000000000 : ℝ) ≤ agent11884.frame ∧
    (1457123715916900025721 / 200000000000000000000000 : ℝ) ≤ agent11884.root ∧
    scalar11884.worldRadius ≤ (2382811699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (643897340484004489391 / 500000000000000000000000 : ℝ) ≤ agent11884.charge ∧
    (1303160226161363757191 / 1000000000000000000000000 : ℝ) ≤ scalar11884.upperTail ∧
    (1662715193067238817183 / 1000000000000000000000000 : ℝ) ≤ scalar11884.lowerTail ∧
    scalar11884.totalBudget ≤ (795140466559391055633 / 100000000000000000000000 : ℝ) := by
  norm_num only [world11884, agent11884, scalar11884] <;> simp only [true_and]

theorem source_rounding11885 :
    (605901148452784624609 / 500000000000000000000000 : ℝ) ≤ world11885.hiddenCharge ∧
    (637701920848761352653473 / 1000000000000000000000000 : ℝ) ≤ world11885.frame ∧
    (5603859059 / 500000000000000000 : ℝ) ≤ world11885.moment ∧
    (368724046757830050864173 / 250000000000000000000000 : ℝ) ≤ agent11885.frame ∧
    (3642467437307820326287 / 500000000000000000000000 : ℝ) ≤ agent11885.root ∧
    scalar11885.worldRadius ≤ (2383225799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (32187665742502009233 / 25000000000000000000000 : ℝ) ≤ agent11885.charge ∧
    (52079175392795049859 / 40000000000000000000000 : ℝ) ≤ scalar11885.upperTail ∧
    (103832561612715500881 / 62500000000000000000000 : ℝ) ≤ scalar11885.lowerTail ∧
    scalar11885.totalBudget ≤ (7947653729656732481861 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11885, agent11885, scalar11885] <;> simp only [true_and]

theorem source_rounding11886 :
    (151468473558694874921 / 125000000000000000000000 : ℝ) ≤ world11886.hiddenCharge ∧
    (637686060080932668391811 / 1000000000000000000000000 : ℝ) ≤ world11886.frame ∧
    (11205246929 / 1000000000000000000 : ℝ) ≤ world11886.moment ∧
    (73742493014567790915547 / 50000000000000000000000 : ℝ) ≤ agent11886.frame ∧
    (364212574695058362503 / 50000000000000000000000 : ℝ) ≤ agent11886.root ∧
    scalar11886.worldRadius ≤ (2383639999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1287218866683385576219 / 1000000000000000000000000 : ℝ) ≤ agent11886.charge ∧
    (650399982187720265763 / 500000000000000000000000 : ℝ) ≤ scalar11886.upperTail ∧
    (414982090994082858211 / 250000000000000000000000 : ℝ) ≤ scalar11886.lowerTail ∧
    scalar11886.totalBudget ≤ (397195322195820958003 / 50000000000000000000000 : ℝ) := by
  norm_num only [world11886, agent11886, scalar11886] <;> simp only [true_and]

theorem source_rounding11887 :
    (121169329548986975087 / 100000000000000000000000 : ℝ) ≤ world11887.hiddenCharge ∧
    (159417550518004394158383 / 250000000000000000000000 : ℝ) ≤ world11887.frame ∧
    (5601388251 / 500000000000000000 : ℝ) ≤ world11887.moment ∧
    (1474803558546208820047891 / 1000000000000000000000000 : ℝ) ≤ agent11887.frame ∧
    (455223017306328744939 / 62500000000000000000000 : ℝ) ≤ agent11887.root ∧
    scalar11887.worldRadius ≤ (2384054199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (80433211974462763287 / 62500000000000000000000 : ℝ) ≤ agent11887.charge ∧
    (1299621742555936542567 / 1000000000000000000000000 : ℝ) ≤ scalar11887.upperTail ∧
    (829268537480182684863 / 500000000000000000000000 : ℝ) ≤ scalar11887.lowerTail ∧
    scalar11887.totalBudget ≤ (1588032499709672742349 / 200000000000000000000000 : ℝ) := by
  norm_num only [world11887, agent11887, scalar11887] <;> simp only [true_and]

theorem source_rounding11888 :
    (1211638817960768606911 / 1000000000000000000000000 : ℝ) ≤ world11888.hiddenCharge ∧
    (79706793352656425051503 / 125000000000000000000000 : ℝ) ≤ world11888.frame ∧
    (2240061367 / 200000000000000000 : ℝ) ≤ world11888.moment ∧
    (1474757275809593955280513 / 1000000000000000000000000 : ℝ) ≤ agent11888.frame ∧
    (7282885383779714874751 / 1000000000000000000000000 : ℝ) ≤ agent11888.root ∧
    scalar11888.worldRadius ≤ (2384468199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (160830525512253873403 / 125000000000000000000000 : ℝ) ≤ agent11888.charge ∧
    (1298444662305100687997 / 1000000000000000000000000 : ℝ) ≤ scalar11888.upperTail ∧
    (1657147036728867752507 / 1000000000000000000000000 : ℝ) ≤ scalar11888.lowerTail ∧
    scalar11888.totalBudget ≤ (158728441685839982227 / 20000000000000000000000 : ℝ) := by
  norm_num only [world11888, agent11888, scalar11888] <;> simp only [true_and]

theorem source_rounding11889 :
    (302896088969130586951 / 250000000000000000000000 : ℝ) ≤ world11889.hiddenCharge ∧
    (637638494327869956831449 / 1000000000000000000000000 : ℝ) ≤ world11889.frame ∧
    (1399729741 / 125000000000000000 : ℝ) ≤ world11889.moment ∧
    (737355512004904463691741 / 500000000000000000000000 : ℝ) ≤ agent11889.frame ∧
    (1456440530813092406939 / 200000000000000000000000 : ℝ) ≤ agent11889.root ∧
    scalar11889.worldRadius ≤ (2384882399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (257271460775515022799 / 200000000000000000000000 : ℝ) ≤ agent11889.charge ∧
    (259453790738437052851 / 200000000000000000000000 : ℝ) ≤ scalar11889.upperTail ∧
    (51742454323565039259 / 31250000000000000000000 : ℝ) ≤ scalar11889.lowerTail ∧
    scalar11889.totalBudget ≤ (991585632377740209831 / 125000000000000000000000 : ℝ) := by
  norm_num only [world11889, agent11889, scalar11889] <;> simp only [true_and]

theorem source_rounding11890 :
    (605764954615701756461 / 500000000000000000000000 : ℝ) ≤ world11890.hiddenCharge ∧
    (159405661147777292202403 / 250000000000000000000000 : ℝ) ≤ world11890.frame ∧
    (5597684891 / 500000000000000000 : ℝ) ≤ world11890.moment ∧
    (1474664797160335616540619 / 1000000000000000000000000 : ℝ) ≤ agent11890.frame ∧
    (455095015490896350663 / 62500000000000000000000 : ℝ) ≤ agent11890.root ∧
    scalar11890.worldRadius ≤ (2385296499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (643035345302379861117 / 500000000000000000000000 : ℝ) ≤ agent11890.charge ∧
    (1296094483424015807629 / 1000000000000000000000000 : ℝ) ≤ scalar11890.upperTail ∧
    (330874281663153638683 / 200000000000000000000000 : ℝ) ≤ scalar11890.lowerTail ∧
    scalar11890.totalBudget ≤ (3964475806022203700331 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11890, agent11890, scalar11890] <;> simp only [true_and]

theorem source_rounding11891 :
    (24229509560393656003 / 20000000000000000000000 : ℝ) ≤ world11891.hiddenCharge ∧
    (159401699402551311368971 / 250000000000000000000000 : ℝ) ≤ world11891.frame ∧
    (2798225599 / 250000000000000000 : ℝ) ≤ world11891.moment ∧
    (184327323659469032548971 / 125000000000000000000000 : ℝ) ≤ agent11891.frame ∧
    (1820209501185996147127 / 250000000000000000000000 : ℝ) ≤ agent11891.root ∧
    scalar11891.worldRadius ≤ (2385710699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (321446090988680317003 / 250000000000000000000000 : ℝ) ≤ agent11891.charge ∧
    (1294921257857319167581 / 1000000000000000000000000 : ℝ) ≤ scalar11891.upperTail ∧
    (12913950487542845313 / 7812500000000000000000 : ℝ) ≤ scalar11891.lowerTail ∧
    scalar11891.totalBudget ≤ (7925221435335194202091 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11891, agent11891, scalar11891] <;> simp only [true_and]

theorem source_rounding11892 :
    (1211421062235639698181 / 1000000000000000000000000 : ℝ) ≤ world11892.hiddenCharge ∧
    (637590953384394874989357 / 1000000000000000000000000 : ℝ) ≤ world11892.frame ∧
    (11190435769 / 1000000000000000000 : ℝ) ≤ world11892.moment ∧
    (737286206141397376268493 / 500000000000000000000000 : ℝ) ≤ agent11892.frame ∧
    (3640078042381160935399 / 500000000000000000000000 : ℝ) ≤ agent11892.root ∧
    scalar11892.worldRadius ≤ (2386124799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1285498323603008946369 / 1000000000000000000000000 : ℝ) ≤ agent11892.charge ∧
    (646874645699881049317 / 500000000000000000000000 : ℝ) ≤ scalar11892.upperTail ∧
    (1651601313113307591589 / 1000000000000000000000000 : ℝ) ≤ scalar11892.lowerTail ∧
    scalar11892.totalBudget ≤ (1584298976801396457741 / 200000000000000000000000 : ℝ) := by
  norm_num only [world11892, agent11892, scalar11892] <;> simp only [true_and]

theorem source_rounding11893 :
    (605683330936775167801 / 500000000000000000000000 : ℝ) ≤ world11893.hiddenCharge ∧
    (79696888989114357953397 / 125000000000000000000000 : ℝ) ≤ world11893.frame ∧
    (5593984951 / 500000000000000000 : ℝ) ≤ world11893.moment ∧
    (737263127112861726928047 / 500000000000000000000000 : ℝ) ≤ agent11893.frame ∧
    (7279474327575636711141 / 1000000000000000000000000 : ℝ) ≤ agent11893.root ∧
    scalar11893.worldRadius ≤ (2386538999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1285212569225584104473 / 1000000000000000000000000 : ℝ) ≤ agent11893.charge ∧
    (1292578566579080864071 / 1000000000000000000000000 : ℝ) ≤ scalar11893.upperTail ∧
    (412554586179641009283 / 250000000000000000000000 : ℝ) ≤ scalar11893.lowerTail ∧
    scalar11893.totalBudget ≤ (3958885797795783695227 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11893, agent11893, scalar11893] <;> simp only [true_and]

theorem source_rounding11894 :
    (1211312276927698106473 / 1000000000000000000000000 : ℝ) ≤ world11894.hiddenCharge ∧
    (637559273195002294595129 / 1000000000000000000000000 : ℝ) ≤ world11894.frame ∧
    (5592752397 / 500000000000000000 : ℝ) ≤ world11894.moment ∧
    (147448012703023447607627 / 100000000000000000000000 : ℝ) ≤ agent11894.frame ∧
    (1455758562620947501521 / 200000000000000000000000 : ℝ) ≤ agent11894.root ∧
    scalar11894.worldRadius ≤ (2386953099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (128492710049881965571 / 100000000000000000000000 : ℝ) ≤ agent11894.charge ∧
    (10089133109273222897 / 7812500000000000000000 : ℝ) ≤ scalar11894.upperTail ∧
    (1648836705246453947481 / 1000000000000000000000000 : ℝ) ≤ scalar11894.lowerTail ∧
    scalar11894.totalBudget ≤ (989256475216417844099 / 125000000000000000000000 : ℝ) := by
  norm_num only [world11894, agent11894, scalar11894] <;> simp only [true_and]

theorem source_rounding11895 :
    (151407238424045760123 / 125000000000000000000000 : ℝ) ≤ world11895.hiddenCharge ∧
    (63754343722989465059223 / 100000000000000000000000 : ℝ) ≤ world11895.frame ∧
    (2795760111 / 250000000000000000 : ℝ) ≤ world11895.moment ∧
    (737217009370850300042137 / 500000000000000000000000 : ℝ) ≤ agent11895.frame ∧
    (7278111621202290567693 / 1000000000000000000000000 : ℝ) ≤ agent11895.root ∧
    scalar11895.worldRadius ≤ (2387367099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (80290119818718718419 / 62500000000000000000000 : ℝ) ≤ agent11895.charge ∧
    (322560179081255219141 / 250000000000000000000000 : ℝ) ≤ scalar11895.upperTail ∧
    (823728197322650098969 / 500000000000000000000000 : ℝ) ≤ scalar11895.lowerTail ∧
    scalar11895.totalBudget ≤ (3955167755179332326971 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11895, agent11895, scalar11895] <;> simp only [true_and]

theorem source_rounding11896 :
    (605601776630920777459 / 500000000000000000000000 : ℝ) ≤ world11896.hiddenCharge ∧
    (159381901004207424744303 / 250000000000000000000000 : ℝ) ≤ world11896.frame ∧
    (11180576853 / 1000000000000000000 : ℝ) ≤ world11896.moment ∧
    (1474387941284779320348661 / 1000000000000000000000000 : ℝ) ≤ agent11896.frame ∧
    (1455486118327517924199 / 200000000000000000000000 : ℝ) ≤ agent11896.root ∧
    scalar11896.worldRadius ≤ (2387781299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1284357018704817913269 / 1000000000000000000000000 : ℝ) ≤ agent11896.charge ∧
    (1289073754906422663327 / 1000000000000000000000000 : ℝ) ≤ scalar11896.upperTail ∧
    (823038805921013579463 / 500000000000000000000000 : ℝ) ≤ scalar11896.lowerTail ∧
    scalar11896.totalBudget ≤ (3953311291130823141357 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11896, agent11896, scalar11896] <;> simp only [true_and]

theorem source_rounding11897 :
    (30278730363260287571 / 25000000000000000000000 : ℝ) ≤ world11897.hiddenCharge ∧
    (318755886777522656638197 / 500000000000000000000000 : ℝ) ≤ world11897.frame ∧
    (558905701 / 50000000000000000 : ℝ) ≤ world11897.moment ∧
    (184292735338244310293909 / 125000000000000000000000 : ℝ) ≤ agent11897.frame ∧
    (727674988426887287639 / 100000000000000000000000 : ℝ) ≤ agent11897.root ∧
    scalar11897.worldRadius ≤ (2388195399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (642036202496189508637 / 500000000000000000000000 : ℝ) ≤ agent11897.charge ∧
    (643953998625901442671 / 500000000000000000000000 : ℝ) ≤ scalar11897.upperTail ∧
    (822350077291737478047 / 500000000000000000000000 : ℝ) ≤ scalar11897.lowerTail ∧
    scalar11897.totalBudget ≤ (123483017961127618067 / 15625000000000000000000 : ℝ) := by
  norm_num only [world11897, agent11897, scalar11897] <;> simp only [true_and]

theorem source_rounding11898 :
    (605547445596185074607 / 500000000000000000000000 : ℝ) ≤ world11898.hiddenCharge ∧
    (637495945843779939859051 / 1000000000000000000000000 : ℝ) ≤ world11898.frame ∧
    (1396956493 / 125000000000000000 : ℝ) ≤ world11898.moment ∧
    (1474295854928846127004629 / 1000000000000000000000000 : ℝ) ≤ agent11898.frame ∧
    (7276069338933964463491 / 1000000000000000000000000 : ℝ) ≤ agent11898.root ∧
    scalar11898.worldRadius ≤ (2388609499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1283788075640196144449 / 1000000000000000000000000 : ℝ) ≤ agent11898.charge ∧
    (160842930712758807953 / 125000000000000000000000 : ℝ) ≤ scalar11898.upperTail ∧
    (821662022181775044683 / 500000000000000000000000 : ℝ) ≤ scalar11898.lowerTail ∧
    scalar11898.totalBudget ≤ (3949603535106091213571 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11898, agent11898, scalar11898] <;> simp only [true_and]

theorem source_rounding11899 :
    (151380072905251424247 / 125000000000000000000000 : ℝ) ≤ world11899.hiddenCharge ∧
    (637480120882272013576393 / 1000000000000000000000000 : ℝ) ≤ world11899.frame ∧
    (11173190627 / 1000000000000000000 : ℝ) ≤ world11899.moment ∧
    (294849969200209562079451 / 200000000000000000000000 : ℝ) ≤ agent11899.frame ∧
    (727538903546931594229 / 100000000000000000000000 : ℝ) ≤ agent11899.root ∧
    scalar11899.worldRadius ≤ (2389023599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (12835040303266912831 / 10000000000000000000000 : ℝ) ≤ agent11899.charge ∧
    (1285580110880758549199 / 1000000000000000000000000 : ℝ) ≤ scalar11899.upperTail ∧
    (82097464053617656131 / 50000000000000000000000 : ℝ) ≤ scalar11899.lowerTail ∧
    scalar11899.totalBudget ≤ (197387608898260223833 / 25000000000000000000000 : ℝ) := by
  norm_num only [world11899, agent11899, scalar11899] <;> simp only [true_and]

theorem source_rounding11900 :
    (30274657266840796037 / 25000000000000000000000 : ℝ) ≤ world11900.hiddenCharge ∧
    (637464298669760452874783 / 1000000000000000000000000 : ℝ) ≤ world11900.frame ∧
    (5585365033 / 500000000000000000 : ℝ) ≤ world11900.moment ∧
    (368550965469234057046967 / 250000000000000000000000 : ℝ) ≤ agent11900.frame ∧
    (3637354526821677374487 / 500000000000000000000000 : ℝ) ≤ agent11900.root ∧
    scalar11900.worldRadius ≤ (2389437799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (16040253359133681147 / 12500000000000000000000 : ℝ) ≤ agent11900.charge ∧
    (1284418149659721472511 / 1000000000000000000000000 : ℝ) ≤ scalar11900.upperTail ∧
    (820288023497681444123 / 500000000000000000000000 : ℝ) ≤ scalar11900.lowerTail ∧
    scalar11900.totalBudget ≤ (7891805180649542008953 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11900, agent11900, scalar11900] <;> simp only [true_and]

theorem source_rounding11901 :
    (242186402696306461937 / 200000000000000000000000 : ℝ) ≤ world11901.hiddenCharge ∧
    (318724239602742246006773 / 500000000000000000000000 : ℝ) ≤ world11901.frame ∧
    (5584135131 / 500000000000000000 : ℝ) ≤ world11901.moment ∧
    (184269737817736890273143 / 125000000000000000000000 : ℝ) ≤ agent11901.frame ∧
    (909253654174591589007 / 125000000000000000000000 : ℝ) ≤ agent11901.root ∧
    scalar11901.worldRadius ≤ (2389851899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1282936790531443319741 / 1000000000000000000000000 : ℝ) ≤ agent11901.charge ∧
    (64162864552965443011 / 50000000000000000000000 : ℝ) ≤ scalar11901.upperTail ∧
    (65568161414820236601 / 40000000000000000000000 : ℝ) ≤ scalar11901.lowerTail ∧
    scalar11901.totalBudget ≤ (7888109293360426322133 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11901, agent11901, scalar11901] <;> simp only [true_and]

theorem source_rounding11902 :
    (242175550332002960919 / 200000000000000000000000 : ℝ) ≤ world11902.hiddenCharge ∧
    (159358165622170881754483 / 250000000000000000000000 : ℝ) ≤ world11902.frame ∧
    (2233162243 / 200000000000000000 : ℝ) ≤ world11902.moment ∧
    (1474111967981326360837203 / 1000000000000000000000000 : ℝ) ≤ agent11902.frame ∧
    (727334965451533097823 / 100000000000000000000000 : ℝ) ≤ agent11902.root ∧
    scalar11902.worldRadius ≤ (2390265999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (641326797704291114311 / 500000000000000000000000 : ℝ) ≤ agent11902.charge ∧
    (1282097668331731135751 / 1000000000000000000000000 : ℝ) ≤ scalar11902.upperTail ∧
    (1637833397218366017417 / 1000000000000000000000000 : ℝ) ≤ scalar11902.lowerTail ∧
    scalar11902.totalBudget ≤ (788441681409360657851 / 100000000000000000000000 : ℝ) := by
  norm_num only [world11902, agent11902, scalar11902] <;> simp only [true_and]

theorem source_rounding11903 :
    (1210823505203382522327 / 1000000000000000000000000 : ℝ) ≤ world11903.hiddenCharge ∧
    (318708424259298589931259 / 500000000000000000000000 : ℝ) ≤ world11903.frame ∧
    (446534117 / 40000000000000000 : ℝ) ≤ world11903.moment ∧
    (737033029090324957774163 / 500000000000000000000000 : ℝ) ≤ agent11903.frame ∧
    (7272670396717077248847 / 1000000000000000000000000 : ℝ) ≤ agent11903.root ∧
    scalar11903.worldRadius ≤ (2390680099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (641185341521081007319 / 500000000000000000000000 : ℝ) ≤ agent11903.charge ∧
    (1280939339161522332051 / 1000000000000000000000000 : ℝ) ≤ scalar11903.upperTail ∧
    (1636464194781910619273 / 1000000000000000000000000 : ℝ) ≤ scalar11903.lowerTail ∧
    scalar11903.totalBudget ≤ (7880727862134282897109 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11903, agent11903, scalar11903] <;> simp only [true_and]

theorem source_rounding11904 :
    (302692318526486094251 / 250000000000000000000000 : ℝ) ≤ world11904.hiddenCharge ∧
    (159350259323616413317849 / 250000000000000000000000 : ℝ) ≤ world11904.frame ∧
    (1116089539 / 100000000000000000 : ℝ) ≤ world11904.moment ∧
    (184252521640662979628431 / 125000000000000000000000 : ℝ) ≤ agent11904.frame ∧
    (7271991300045341559139 / 1000000000000000000000000 : ℝ) ≤ agent11904.root ∧
    scalar11904.worldRadius ≤ (2391094299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1282088053112639232003 / 1000000000000000000000000 : ℝ) ≤ agent11904.charge ∧
    (1279782258580429323391 / 1000000000000000000000000 : ℝ) ≤ scalar11904.upperTail ∧
    (163509638691382833889 / 100000000000000000000000 : ℝ) ≤ scalar11904.lowerTail ∧
    scalar11904.totalBudget ≤ (7877042187382547812421 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11904, agent11904, scalar11904] <;> simp only [true_and]

theorem source_rounding11905 :
    (1210715058362010468079 / 1000000000000000000000000 : ℝ) ≤ world11905.hiddenCharge ∧
    (637385228815529086801623 / 1000000000000000000000000 : ℝ) ≤ world11905.frame ∧
    (11158438611 / 1000000000000000000 : ℝ) ≤ world11905.moment ∧
    (3684935782001860579171 / 2500000000000000000000 : ℝ) ≤ agent11905.frame ∧
    (7271312524087410211431 / 1000000000000000000000000 : ℝ) ≤ agent11905.root ∧
    scalar11905.worldRadius ≤ (2391508399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (640902852650437808559 / 500000000000000000000000 : ℝ) ≤ agent11905.charge ∧
    (1278626393290124094007 / 1000000000000000000000000 : ℝ) ≤ scalar11905.upperTail ∧
    (1633729923134961536677 / 1000000000000000000000000 : ℝ) ≤ scalar11905.lowerTail ∧
    scalar11905.totalBudget ≤ (7873360032128066771899 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11905, agent11905, scalar11905] <;> simp only [true_and]

theorem source_rounding11906 :
    (151332607245736698691 / 125000000000000000000000 : ℝ) ≤ world11906.hiddenCharge ∧
    (637369423081028184486751 / 1000000000000000000000000 : ℝ) ≤ world11906.frame ∧
    (11155982587 / 1000000000000000000 : ℝ) ≤ world11906.moment ∧
    (736964238596222618980919 / 500000000000000000000000 : ℝ) ≤ agent11906.frame ∧
    (454414619309686829171 / 62500000000000000000000 : ℝ) ≤ agent11906.root ∧
    scalar11906.worldRadius ≤ (2391922499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (640761819644068756861 / 500000000000000000000000 : ℝ) ≤ agent11906.charge ∧
    (638735849310035849733 / 500000000000000000000000 : ℝ) ≤ scalar11906.upperTail ∧
    (816182381300921132563 / 500000000000000000000000 : ℝ) ≤ scalar11906.lowerTail ∧
    scalar11906.totalBudget ≤ (7869681146453776641171 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11906, agent11906, scalar11906] <;> simp only [true_and]

theorem source_rounding11907 :
    (605303336455954614101 / 500000000000000000000000 : ℝ) ≤ world11907.hiddenCharge ∧
    (159338405022550954390371 / 250000000000000000000000 : ℝ) ≤ world11907.frame ∧
    (11153527319 / 1000000000000000000 : ℝ) ≤ world11907.moment ∧
    (294776533257179800587767 / 200000000000000000000000 : ℝ) ≤ agent11907.frame ∧
    (3634977767174915336307 / 500000000000000000000000 : ℝ) ≤ agent11907.root ∧
    scalar11907.worldRadius ≤ (2392336499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (128124185475609529893 / 100000000000000000000000 : ℝ) ≤ agent11907.charge ∧
    (1276318157338600775379 / 1000000000000000000000000 : ℝ) ≤ scalar11907.upperTail ∧
    (407750219866053478613 / 250000000000000000000000 : ℝ) ≤ scalar11907.lowerTail ∧
    scalar11907.totalBudget ≤ (1966501412555287293317 / 250000000000000000000000 : ℝ) := by
  norm_num only [world11907, agent11907, scalar11907] <;> simp only [true_and]

theorem source_rounding11908 :
    (1210552503194375562187 / 1000000000000000000000000 : ℝ) ≤ world11908.hiddenCharge ∧
    (637337819842297120309737 / 1000000000000000000000000 : ℝ) ≤ world11908.frame ∧
    (2230214561 / 200000000000000000 : ℝ) ≤ world11908.moment ∧
    (29476737482010920248189 / 20000000000000000000000 : ℝ) ≤ agent11908.frame ∧
    (1453855480020980802981 / 200000000000000000000000 : ℝ) ≤ agent11908.root ∧
    scalar11908.worldRadius ≤ (2392750699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1280960351386822810191 / 1000000000000000000000000 : ℝ) ≤ agent11908.charge ∧
    (637582984494975614911 / 500000000000000000000000 : ℝ) ≤ scalar11908.upperTail ∧
    (325927701021380697543 / 200000000000000000000000 : ℝ) ≤ scalar11908.lowerTail ∧
    scalar11908.totalBudget ≤ (3931166741789203753463 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11908, agent11908, scalar11908] <;> simp only [true_and]

noncomputable def paperAgent11884 : AgentParameters :=
  { agent11884 with charge := (321948671 / 250000000000 : ℝ) }

theorem agent_is_repriced11884 : agent11884 =
    BstLean.Part265.agentRepriced 11884 world11884 paperAgent11884 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11884, agent11884]

noncomputable def paperAgent11885 : AgentParameters :=
  { agent11885 with charge := (1287506633 / 1000000000000 : ℝ) }

theorem agent_is_repriced11885 : agent11885 =
    BstLean.Part265.agentRepriced 11885 world11885 paperAgent11885 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11885, agent11885]

noncomputable def paperAgent11886 : AgentParameters :=
  { agent11886 with charge := (128721887 / 100000000000 : ℝ) }

theorem agent_is_repriced11886 : agent11886 =
    BstLean.Part265.agentRepriced 11886 world11886 paperAgent11886 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11886, agent11886]

noncomputable def paperAgent11887 : AgentParameters :=
  { agent11887 with charge := (257386279 / 200000000000 : ℝ) }

theorem agent_is_repriced11887 : agent11887 =
    BstLean.Part265.agentRepriced 11887 world11887 paperAgent11887 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11887, agent11887]

noncomputable def paperAgent11888 : AgentParameters :=
  { agent11888 with charge := (80415263 / 62500000000 : ℝ) }

theorem agent_is_repriced11888 : agent11888 =
    BstLean.Part265.agentRepriced 11888 world11888 paperAgent11888 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11888, agent11888]

noncomputable def paperAgent11889 : AgentParameters :=
  { agent11889 with charge := (1286357307 / 1000000000000 : ℝ) }

theorem agent_is_repriced11889 : agent11889 =
    BstLean.Part265.agentRepriced 11889 world11889 paperAgent11889 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11889, agent11889]

noncomputable def paperAgent11890 : AgentParameters :=
  { agent11890 with charge := (643035347 / 500000000000 : ℝ) }

theorem agent_is_repriced11890 : agent11890 =
    BstLean.Part265.agentRepriced 11890 world11890 paperAgent11890 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11890, agent11890]

noncomputable def paperAgent11891 : AgentParameters :=
  { agent11891 with charge := (1285784367 / 1000000000000 : ℝ) }

theorem agent_is_repriced11891 : agent11891 =
    BstLean.Part265.agentRepriced 11891 world11891 paperAgent11891 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11891, agent11891]

noncomputable def paperAgent11892 : AgentParameters :=
  { agent11892 with charge := (1285498327 / 1000000000000 : ℝ) }

theorem agent_is_repriced11892 : agent11892 =
    BstLean.Part265.agentRepriced 11892 world11892 paperAgent11892 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11892, agent11892]

noncomputable def paperAgent11893 : AgentParameters :=
  { agent11893 with charge := (1285212573 / 1000000000000 : ℝ) }

theorem agent_is_repriced11893 : agent11893 =
    BstLean.Part265.agentRepriced 11893 world11893 paperAgent11893 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11893, agent11893]

noncomputable def paperAgent11894 : AgentParameters :=
  { agent11894 with charge := (10038493 / 7812500000 : ℝ) }

theorem agent_is_repriced11894 : agent11894 =
    BstLean.Part265.agentRepriced 11894 world11894 paperAgent11894 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11894, agent11894]

noncomputable def paperAgent11895 : AgentParameters :=
  { agent11895 with charge := (1284641921 / 1000000000000 : ℝ) }

theorem agent_is_repriced11895 : agent11895 =
    BstLean.Part265.agentRepriced 11895 world11895 paperAgent11895 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11895, agent11895]

noncomputable def paperAgent11896 : AgentParameters :=
  { agent11896 with charge := (642178511 / 500000000000 : ℝ) }

theorem agent_is_repriced11896 : agent11896 =
    BstLean.Part265.agentRepriced 11896 world11896 paperAgent11896 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11896, agent11896]

noncomputable def paperAgent11897 : AgentParameters :=
  { agent11897 with charge := (160509051 / 125000000000 : ℝ) }

theorem agent_is_repriced11897 : agent11897 =
    BstLean.Part265.agentRepriced 11897 world11897 paperAgent11897 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11897, agent11897]

noncomputable def paperAgent11898 : AgentParameters :=
  { agent11898 with charge := (1283788079 / 1000000000000 : ℝ) }

theorem agent_is_repriced11898 : agent11898 =
    BstLean.Part265.agentRepriced 11898 world11898 paperAgent11898 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11898, agent11898]

noncomputable def paperAgent11899 : AgentParameters :=
  { agent11899 with charge := (641752017 / 500000000000 : ℝ) }

theorem agent_is_repriced11899 : agent11899 =
    BstLean.Part265.agentRepriced 11899 world11899 paperAgent11899 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11899, agent11899]

noncomputable def paperAgent11900 : AgentParameters :=
  { agent11900 with charge := (80201267 / 62500000000 : ℝ) }

theorem agent_is_repriced11900 : agent11900 =
    BstLean.Part265.agentRepriced 11900 world11900 paperAgent11900 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11900, agent11900]

noncomputable def paperAgent11901 : AgentParameters :=
  { agent11901 with charge := (641468397 / 500000000000 : ℝ) }

theorem agent_is_repriced11901 : agent11901 =
    BstLean.Part265.agentRepriced 11901 world11901 paperAgent11901 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11901, agent11901]

noncomputable def paperAgent11902 : AgentParameters :=
  { agent11902 with charge := (1282653599 / 1000000000000 : ℝ) }

theorem agent_is_repriced11902 : agent11902 =
    BstLean.Part265.agentRepriced 11902 world11902 paperAgent11902 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11902, agent11902]

noncomputable def paperAgent11903 : AgentParameters :=
  { agent11903 with charge := (1282370687 / 1000000000000 : ℝ) }

theorem agent_is_repriced11903 : agent11903 =
    BstLean.Part265.agentRepriced 11903 world11903 paperAgent11903 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11903, agent11903]

noncomputable def paperAgent11904 : AgentParameters :=
  { agent11904 with charge := (1282088057 / 1000000000000 : ℝ) }

theorem agent_is_repriced11904 : agent11904 =
    BstLean.Part265.agentRepriced 11904 world11904 paperAgent11904 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11904, agent11904]

noncomputable def paperAgent11905 : AgentParameters :=
  { agent11905 with charge := (1281805709 / 1000000000000 : ℝ) }

theorem agent_is_repriced11905 : agent11905 =
    BstLean.Part265.agentRepriced 11905 world11905 paperAgent11905 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11905, agent11905]

noncomputable def paperAgent11906 : AgentParameters :=
  { agent11906 with charge := (1281523643 / 1000000000000 : ℝ) }

theorem agent_is_repriced11906 : agent11906 =
    BstLean.Part265.agentRepriced 11906 world11906 paperAgent11906 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11906, agent11906]

noncomputable def paperAgent11907 : AgentParameters :=
  { agent11907 with charge := (640620929 / 500000000000 : ℝ) }

theorem agent_is_repriced11907 : agent11907 =
    BstLean.Part265.agentRepriced 11907 world11907 paperAgent11907 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11907, agent11907]

noncomputable def paperAgent11908 : AgentParameters :=
  { agent11908 with charge := (256192071 / 200000000000 : ℝ) }

theorem agent_is_repriced11908 : agent11908 =
    BstLean.Part265.agentRepriced 11908 world11908 paperAgent11908 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11908, agent11908]

end BstLean.Part281
