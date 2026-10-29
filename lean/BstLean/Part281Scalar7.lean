import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 12034 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12034. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12034 : WorldParameters where
  hiddenCharge := (240769583 / 200000000000 : ℝ)
  frame := (15884216969 / 25000000000 : ℝ)
  moment := (2714960867 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12034 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1506183579877 / 1000000000000 : ℝ)
    root := (1894352981 / 250000000000 : ℝ) }

noncomputable def scalar12034 : ScalarCertificate 12034 world12034 agent12034 where
  dimensionLo := 12034
  dimensionHi := 12034
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2282790599 / 1000000000000 : ℝ)
  frameLo := (15884216969 / 25000000000 : ℝ)
  frameHi := (1506183579877 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12034]
  agentFrame_pos := by norm_num only [agent12034]
  worldRadius := (2282790599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12034]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (292109863 / 200000000000 : ℝ)
  lowerTail := (1838466629 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8385979623 / 1000000000000 : ℝ)
  ledger := by
    have h : (240769583 / 200000000000 : ℚ) +
        (2714960867 / 250000000000000000 : ℚ) / (2282790599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (292109863 / 200000000000 : ℚ) + (1838466629 / 1000000000000 : ℚ) ≤
        (8385979623 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((240769583 / 200000000000 : ℚ) +
        (2714960867 / 250000000000000000 : ℚ) / (2282790599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (292109863 / 200000000000 : ℚ) + (1838466629 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8385979623 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12034]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12034 :
    2 * 160 < 12034 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999387 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12034 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12035 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12035. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12035 : WorldParameters where
  hiddenCharge := (1203795647 / 1000000000000 : ℝ)
  frame := (635353220793 / 1000000000000 : ℝ)
  moment := (2714370087 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12035 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (753066170009 / 500000000000 : ℝ)
    root := (3788357323 / 500000000000 : ℝ) }

noncomputable def scalar12035 : ScalarCertificate 12035 world12035 agent12035 where
  dimensionLo := 12035
  dimensionHi := 12035
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2283192499 / 1000000000000 : ℝ)
  frameLo := (635353220793 / 1000000000000 : ℝ)
  frameHi := (753066170009 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12035]
  agentFrame_pos := by norm_num only [agent12035]
  worldRadius := (2283192499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12035]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (22800303 / 15625000000 : ℝ)
  lowerTail := (1836914363 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (33527433 / 4000000000 : ℝ)
  ledger := by
    have h : (1203795647 / 1000000000000 : ℚ) +
        (2714370087 / 250000000000000000 : ℚ) / (2283192499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (22800303 / 15625000000 : ℚ) + (1836914363 / 1000000000000 : ℚ) ≤
        (33527433 / 4000000000 : ℚ) := by norm_num only
    have hc : (((1203795647 / 1000000000000 : ℚ) +
        (2714370087 / 250000000000000000 : ℚ) / (2283192499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (22800303 / 15625000000 : ℚ) + (1836914363 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((33527433 / 4000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12035]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12035 :
    2 * 160 < 12035 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997189 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12035 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12036 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12036. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12036 : WorldParameters where
  hiddenCharge := (240748679 / 200000000000 : ℝ)
  frame := (25413510619 / 40000000000 : ℝ)
  moment := (5427558973 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12036 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (301216225089 / 200000000000 : ℝ)
    root := (7576017677 / 1000000000000 : ℝ) }

noncomputable def scalar12036 : ScalarCertificate 12036 world12036 agent12036 where
  dimensionLo := 12036
  dimensionHi := 12036
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2283594299 / 1000000000000 : ℝ)
  frameLo := (25413510619 / 40000000000 : ℝ)
  frameHi := (301216225089 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12036]
  agentFrame_pos := by norm_num only [agent12036]
  worldRadius := (2283594299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12036]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1457890849 / 1000000000000 : ℝ)
  lowerTail := (917681803 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8377740809 / 1000000000000 : ℝ)
  ledger := by
    have h : (240748679 / 200000000000 : ℚ) +
        (5427558973 / 500000000000000000 : ℚ) / (2283594299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1457890849 / 1000000000000 : ℚ) + (917681803 / 500000000000 : ℚ) ≤
        (8377740809 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((240748679 / 200000000000 : ℚ) +
        (5427558973 / 500000000000000000 : ℚ) / (2283594299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1457890849 / 1000000000000 : ℚ) + (917681803 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8377740809 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12036]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12036 :
    2 * 160 < 12036 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998393 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12036 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12037 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12037. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12037 : WorldParameters where
  hiddenCharge := (1203691157 / 1000000000000 : ℝ)
  frame := (158830578201 / 250000000000 : ℝ)
  moment := (5426378131 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12037 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (753014971111 / 500000000000 : ℝ)
    root := (378766043 / 50000000000 : ℝ) }

noncomputable def scalar12037 : ScalarCertificate 12037 world12037 agent12037 where
  dimensionLo := 12037
  dimensionHi := 12037
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2283996099 / 1000000000000 : ℝ)
  frameLo := (158830578201 / 250000000000 : ℝ)
  frameHi := (753014971111 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12037]
  agentFrame_pos := by norm_num only [agent12037]
  worldRadius := (2283996099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12037]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (291312733 / 200000000000 : ℝ)
  lowerTail := (36676287 / 20000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4186813543 / 500000000000 : ℝ)
  ledger := by
    have h : (1203691157 / 1000000000000 : ℚ) +
        (5426378131 / 500000000000000000 : ℚ) / (2283996099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (291312733 / 200000000000 : ℚ) + (36676287 / 20000000000 : ℚ) ≤
        (4186813543 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1203691157 / 1000000000000 : ℚ) +
        (5426378131 / 500000000000000000 : ℚ) / (2283996099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (291312733 / 200000000000 : ℚ) + (36676287 / 20000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4186813543 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12037]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12037 :
    2 * 160 < 12037 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1099999821 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12037 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12038 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12038. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12038 : WorldParameters where
  hiddenCharge := (1203638933 / 1000000000000 : ℝ)
  frame := (635306862779 / 1000000000000 : ℝ)
  moment := (339074853 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12038 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (752989395163 / 500000000000 : ℝ)
    root := (473414017 / 62500000000 : ℝ) }

noncomputable def scalar12038 : ScalarCertificate 12038 world12038 agent12038 where
  dimensionLo := 12038
  dimensionHi := 12038
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2284397899 / 1000000000000 : ℝ)
  frameLo := (635306862779 / 1000000000000 : ℝ)
  frameHi := (752989395163 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12038]
  agentFrame_pos := by norm_num only [agent12038]
  worldRadius := (2284397899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12038]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (291047581 / 200000000000 : ℝ)
  lowerTail := (916133331 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8369517213 / 1000000000000 : ℝ)
  ledger := by
    have h : (1203638933 / 1000000000000 : ℚ) +
        (339074853 / 31250000000000000 : ℚ) / (2284397899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (291047581 / 200000000000 : ℚ) + (916133331 / 500000000000 : ℚ) ≤
        (8369517213 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1203638933 / 1000000000000 : ℚ) +
        (339074853 / 31250000000000000 : ℚ) / (2284397899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (291047581 / 200000000000 : ℚ) + (916133331 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8369517213 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12038]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12038 :
    2 * 160 < 12038 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (549999931 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12038 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12039 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12039. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12039 : WorldParameters where
  hiddenCharge := (48143469 / 40000000000 : ℝ)
  frame := (635291415401 / 1000000000000 : ℝ)
  moment := (10848035047 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12039 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (301185533947 / 200000000000 : ℝ)
    root := (7573927993 / 1000000000000 : ℝ) }

noncomputable def scalar12039 : ScalarCertificate 12039 world12039 agent12039 where
  dimensionLo := 12039
  dimensionHi := 12039
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2284799799 / 1000000000000 : ℝ)
  frameLo := (635291415401 / 1000000000000 : ℝ)
  frameHi := (301185533947 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12039]
  agentFrame_pos := by norm_num only [agent12039]
  worldRadius := (2284799799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12039]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (290782743 / 200000000000 : ℝ)
  lowerTail := (1830720707 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8365411317 / 1000000000000 : ℝ)
  ledger := by
    have h : (48143469 / 40000000000 : ℚ) +
        (10848035047 / 1000000000000000000 : ℚ) / (2284799799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (290782743 / 200000000000 : ℚ) + (1830720707 / 1000000000000 : ℚ) ≤
        (8365411317 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((48143469 / 40000000000 : ℚ) +
        (10848035047 / 1000000000000000000 : ℚ) / (2284799799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (290782743 / 200000000000 : ℚ) + (1830720707 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8365411317 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12039]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12039 :
    2 * 160 < 12039 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998993 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12039 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12040 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12040. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12040 : WorldParameters where
  hiddenCharge := (120353453 / 100000000000 : ℝ)
  frame := (635275970667 / 1000000000000 : ℝ)
  moment := (2711418879 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12040 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1505876580427 / 1000000000000 : ℝ)
    root := (1514646373 / 200000000000 : ℝ) }

noncomputable def scalar12040 : ScalarCertificate 12040 world12040 agent12040 where
  dimensionLo := 12040
  dimensionHi := 12040
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2285201699 / 1000000000000 : ℝ)
  frameLo := (635275970667 / 1000000000000 : ℝ)
  frameHi := (1505876580427 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12040]
  agentFrame_pos := by norm_num only [agent12040]
  worldRadius := (2285201699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12040]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1452590879 / 1000000000000 : ℝ)
  lowerTail := (228647031 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8361309127 / 1000000000000 : ℝ)
  ledger := by
    have h : (120353453 / 100000000000 : ℚ) +
        (2711418879 / 250000000000000000 : ℚ) / (2285201699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1452590879 / 1000000000000 : ℚ) + (228647031 / 125000000000 : ℚ) ≤
        (8361309127 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((120353453 / 100000000000 : ℚ) +
        (2711418879 / 250000000000000000 : ℚ) / (2285201699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1452590879 / 1000000000000 : ℚ) + (228647031 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8361309127 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12040]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12040 :
    2 * 160 < 12040 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (274999907 / 25000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12040 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12041 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12041. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12041 : WorldParameters where
  hiddenCharge := (1203482351 / 1000000000000 : ℝ)
  frame := (635260528579 / 1000000000000 : ℝ)
  moment := (10843316701 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12041 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1505825516291 / 1000000000000 : ℝ)
    root := (1893134011 / 250000000000 : ℝ) }

noncomputable def scalar12041 : ScalarCertificate 12041 world12041 agent12041 where
  dimensionLo := 12041
  dimensionHi := 12041
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2285603399 / 1000000000000 : ℝ)
  frameLo := (635260528579 / 1000000000000 : ℝ)
  frameHi := (1505825516291 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12041]
  agentFrame_pos := by norm_num only [agent12041]
  worldRadius := (2285603399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12041]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1451269331 / 1000000000000 : ℝ)
  lowerTail := (1827633191 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1671442169 / 200000000000 : ℝ)
  ledger := by
    have h : (1203482351 / 1000000000000 : ℚ) +
        (10843316701 / 1000000000000000000 : ℚ) / (2285603399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1451269331 / 1000000000000 : ℚ) + (1827633191 / 1000000000000 : ℚ) ≤
        (1671442169 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1203482351 / 1000000000000 : ℚ) +
        (10843316701 / 1000000000000000000 : ℚ) / (2285603399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1451269331 / 1000000000000 : ℚ) + (1827633191 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1671442169 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12041]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12041 :
    2 * 160 < 12041 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999407 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12041 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12042 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12042. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12042 : WorldParameters where
  hiddenCharge := (601715093 / 500000000000 : ℝ)
  frame := (317622544567 / 500000000000 : ℝ)
  moment := (2710239651 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12042 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1505774489479 / 1000000000000 : ℝ)
    root := (60574723 / 8000000000 : ℝ) }

noncomputable def scalar12042 : ScalarCertificate 12042 world12042 agent12042 where
  dimensionLo := 12042
  dimensionHi := 12042
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2286005299 / 1000000000000 : ℝ)
  frameLo := (317622544567 / 500000000000 : ℝ)
  frameHi := (1505774489479 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12042]
  agentFrame_pos := by norm_num only [agent12042]
  worldRadius := (2286005299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12042]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1449949329 / 1000000000000 : ℝ)
  lowerTail := (114130741 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (52206977 / 6250000000 : ℝ)
  ledger := by
    have h : (601715093 / 500000000000 : ℚ) +
        (2710239651 / 250000000000000000 : ℚ) / (2286005299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1449949329 / 1000000000000 : ℚ) + (114130741 / 62500000000 : ℚ) ≤
        (52206977 / 6250000000 : ℚ) := by norm_num only
    have hc : (((601715093 / 500000000000 : ℚ) +
        (2710239651 / 250000000000000000 : ℚ) / (2286005299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1449949329 / 1000000000000 : ℚ) + (114130741 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((52206977 / 6250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12042]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12042 :
    2 * 160 < 12042 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1099999547 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12042 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12043 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12043. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12043 : WorldParameters where
  hiddenCharge := (240675607 / 200000000000 : ℝ)
  frame := (158807413083 / 250000000000 : ℝ)
  moment := (5419300611 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12043 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (301144697559 / 200000000000 : ℝ)
    root := (1514228987 / 200000000000 : ℝ) }

noncomputable def scalar12043 : ScalarCertificate 12043 world12043 agent12043 where
  dimensionLo := 12043
  dimensionHi := 12043
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2286407099 / 1000000000000 : ℝ)
  frameLo := (158807413083 / 250000000000 : ℝ)
  frameHi := (301144697559 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12043]
  agentFrame_pos := by norm_num only [agent12043]
  worldRadius := (2286407099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12043]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1448630631 / 1000000000000 : ℝ)
  lowerTail := (1824551947 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4174512781 / 500000000000 : ℝ)
  ledger := by
    have h : (240675607 / 200000000000 : ℚ) +
        (5419300611 / 500000000000000000 : ℚ) / (2286407099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1448630631 / 1000000000000 : ℚ) + (1824551947 / 1000000000000 : ℚ) ≤
        (4174512781 / 500000000000 : ℚ) := by norm_num only
    have hc : (((240675607 / 200000000000 : ℚ) +
        (5419300611 / 500000000000000000 : ℚ) / (2286407099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1448630631 / 1000000000000 : ℚ) + (1824551947 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4174512781 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12043]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12043 :
    2 * 160 < 12043 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996311 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12043 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12044 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12044. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12044 : WorldParameters where
  hiddenCharge := (12033259 / 10000000000 : ℝ)
  frame := (158803554543 / 250000000000 : ℝ)
  moment := (10836244557 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12044 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (188209064663 / 125000000000 : ℝ)
    root := (3785224901 / 500000000000 : ℝ) }

noncomputable def scalar12044 : ScalarCertificate 12044 world12044 agent12044 where
  dimensionLo := 12044
  dimensionHi := 12044
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2286808999 / 1000000000000 : ℝ)
  frameLo := (158803554543 / 250000000000 : ℝ)
  frameHi := (188209064663 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12044]
  agentFrame_pos := by norm_num only [agent12044]
  worldRadius := (2286808999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12044]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (723656747 / 500000000000 : ℝ)
  lowerTail := (911506881 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (208623469 / 25000000000 : ℝ)
  ledger := by
    have h : (12033259 / 10000000000 : ℚ) +
        (10836244557 / 1000000000000000000 : ℚ) / (2286808999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (723656747 / 500000000000 : ℚ) + (911506881 / 500000000000 : ℚ) ≤
        (208623469 / 25000000000 : ℚ) := by norm_num only
    have hc : (((12033259 / 10000000000 : ℚ) +
        (10836244557 / 1000000000000000000 : ℚ) / (2286808999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (723656747 / 500000000000 : ℚ) + (911506881 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((208623469 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12044]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12044 :
    2 * 160 < 12044 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995967 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12044 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12045 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12045. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12045 : WorldParameters where
  hiddenCharge := (601636889 / 500000000000 : ℝ)
  frame := (317599393327 / 500000000000 : ℝ)
  moment := (338559019 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12045 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (752810788991 / 500000000000 : ℝ)
    root := (7569754819 / 1000000000000 : ℝ) }

noncomputable def scalar12045 : ScalarCertificate 12045 world12045 agent12045 where
  dimensionLo := 12045
  dimensionHi := 12045
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2287210799 / 1000000000000 : ℝ)
  frameLo := (317599393327 / 500000000000 : ℝ)
  frameHi := (752810788991 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12045]
  agentFrame_pos := by norm_num only [agent12045]
  worldRadius := (2287210799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12045]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1445997619 / 1000000000000 : ℝ)
  lowerTail := (910738483 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4170427821 / 500000000000 : ℝ)
  ledger := by
    have h : (601636889 / 500000000000 : ℚ) +
        (338559019 / 31250000000000000 : ℚ) / (2287210799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1445997619 / 1000000000000 : ℚ) + (910738483 / 500000000000 : ℚ) ≤
        (4170427821 / 500000000000 : ℚ) := by norm_num only
    have hc : (((601636889 / 500000000000 : ℚ) +
        (338559019 / 31250000000000000 : ℚ) / (2287210799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1445997619 / 1000000000000 : ℚ) + (910738483 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4170427821 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12045]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12045 :
    2 * 160 < 12045 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994409 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12045 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12046 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12046. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12046 : WorldParameters where
  hiddenCharge := (150402709 / 125000000000 : ℝ)
  frame := (635183357777 / 1000000000000 : ℝ)
  moment := (5415766687 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12046 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1505570663723 / 1000000000000 : ℝ)
    root := (473066259 / 62500000000 : ℝ) }

noncomputable def scalar12046 : ScalarCertificate 12046 world12046 agent12046 where
  dimensionLo := 12046
  dimensionHi := 12046
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2287612699 / 1000000000000 : ℝ)
  frameLo := (635183357777 / 1000000000000 : ℝ)
  frameHi := (1505570663723 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12046]
  agentFrame_pos := by norm_num only [agent12046]
  worldRadius := (2287612699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12046]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (722341637 / 500000000000 : ℝ)
  lowerTail := (363988371 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (833677641 / 100000000000 : ℝ)
  ledger := by
    have h : (150402709 / 125000000000 : ℚ) +
        (5415766687 / 500000000000000000 : ℚ) / (2287612699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (722341637 / 500000000000 : ℚ) + (363988371 / 200000000000 : ℚ) ≤
        (833677641 / 100000000000 : ℚ) := by norm_num only
    have hc : (((150402709 / 125000000000 : ℚ) +
        (5415766687 / 500000000000000000 : ℚ) / (2287612699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (722341637 / 500000000000 : ℚ) + (363988371 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((833677641 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12046]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12046 :
    2 * 160 < 12046 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (687499847 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12046 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12047 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12047. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12047 : WorldParameters where
  hiddenCharge := (60158479 / 50000000000 : ℝ)
  frame := (31758396577 / 50000000000 : ℝ)
  moment := (2165835771 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12047 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1505519780589 / 1000000000000 : ℝ)
    root := (7568365619 / 1000000000000 : ℝ) }

noncomputable def scalar12047 : ScalarCertificate 12047 world12047 agent12047 where
  dimensionLo := 12047
  dimensionHi := 12047
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2288014499 / 1000000000000 : ℝ)
  frameLo := (31758396577 / 50000000000 : ℝ)
  frameHi := (1505519780589 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12047]
  agentFrame_pos := by norm_num only [agent12047]
  worldRadius := (2288014499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12047]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1443370189 / 1000000000000 : ℝ)
  lowerTail := (181840813 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4166350427 / 500000000000 : ℝ)
  ledger := by
    have h : (60158479 / 50000000000 : ℚ) +
        (2165835771 / 200000000000000000 : ℚ) / (2288014499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1443370189 / 1000000000000 : ℚ) + (181840813 / 100000000000 : ℚ) ≤
        (4166350427 / 500000000000 : ℚ) := by norm_num only
    have hc : (((60158479 / 50000000000 : ℚ) +
        (2165835771 / 200000000000000000 : ℚ) / (2288014499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1443370189 / 1000000000000 : ℚ) + (181840813 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4166350427 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12047]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12047 :
    2 * 160 < 12047 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999857 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12047 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12048 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12048. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12048 : WorldParameters where
  hiddenCharge := (601558751 / 500000000000 : ℝ)
  frame := (635152507943 / 1000000000000 : ℝ)
  moment := (2706706263 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12048 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1505468934641 / 1000000000000 : ℝ)
    root := (3783835661 / 500000000000 : ℝ) }

noncomputable def scalar12048 : ScalarCertificate 12048 world12048 agent12048 where
  dimensionLo := 12048
  dimensionHi := 12048
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2288416399 / 1000000000000 : ℝ)
  frameLo := (635152507943 / 1000000000000 : ℝ)
  frameHi := (1505468934641 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12048]
  agentFrame_pos := by norm_num only [agent12048]
  worldRadius := (2288416399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12048]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (721029309 / 500000000000 : ℝ)
  lowerTail := (363375217 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2082157291 / 250000000000 : ℝ)
  ledger := by
    have h : (601558751 / 500000000000 : ℚ) +
        (2706706263 / 250000000000000000 : ℚ) / (2288416399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (721029309 / 500000000000 : ℚ) + (363375217 / 200000000000 : ℚ) ≤
        (2082157291 / 250000000000 : ℚ) := by norm_num only
    have hc : (((601558751 / 500000000000 : ℚ) +
        (2706706263 / 250000000000000000 : ℚ) / (2288416399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (721029309 / 500000000000 : ℚ) + (363375217 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2082157291 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12048]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12048 :
    2 * 160 < 12048 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994059 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12048 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12049 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12049. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12049 : WorldParameters where
  hiddenCharge := (1203065439 / 1000000000000 : ℝ)
  frame := (79392135873 / 125000000000 : ℝ)
  moment := (10824471963 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12049 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (752709053803 / 500000000000 : ℝ)
    root := (7566977331 / 1000000000000 : ℝ) }

noncomputable def scalar12049 : ScalarCertificate 12049 world12049 agent12049 where
  dimensionLo := 12049
  dimensionHi := 12049
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2288818199 / 1000000000000 : ℝ)
  frameLo := (79392135873 / 125000000000 : ℝ)
  frameHi := (752709053803 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12049]
  agentFrame_pos := by norm_num only [agent12049]
  worldRadius := (2288818199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12049]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (72037419 / 50000000000 : ℝ)
  lowerTail := (453836373 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8324561287 / 1000000000000 : ℝ)
  ledger := by
    have h : (1203065439 / 1000000000000 : ℚ) +
        (10824471963 / 1000000000000000000 : ℚ) / (2288818199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (72037419 / 50000000000 : ℚ) + (453836373 / 250000000000 : ℚ) ≤
        (8324561287 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1203065439 / 1000000000000 : ℚ) +
        (10824471963 / 1000000000000000000 : ℚ) / (2288818199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (72037419 / 50000000000 : ℚ) + (453836373 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8324561287 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12049]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12049 :
    2 * 160 < 12049 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999261 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12049 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12050 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12050. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12050 : WorldParameters where
  hiddenCharge := (1203013391 / 1000000000000 : ℝ)
  frame := (635121668663 / 1000000000000 : ℝ)
  moment := (2705529897 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12050 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1505367317713 / 1000000000000 : ℝ)
    root := (7566283491 / 1000000000000 : ℝ) }

noncomputable def scalar12050 : ScalarCertificate 12050 world12050 agent12050 where
  dimensionLo := 12050
  dimensionHi := 12050
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2289219999 / 1000000000000 : ℝ)
  frameLo := (635121668663 / 1000000000000 : ℝ)
  frameHi := (1505367317713 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12050]
  agentFrame_pos := by norm_num only [agent12050]
  worldRadius := (2289219999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12050]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (287887901 / 200000000000 : ℝ)
  lowerTail := (1813816411 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8320497133 / 1000000000000 : ℝ)
  ledger := by
    have h : (1203013391 / 1000000000000 : ℚ) +
        (2705529897 / 250000000000000000 : ℚ) / (2289219999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (287887901 / 200000000000 : ℚ) + (1813816411 / 1000000000000 : ℚ) ≤
        (8320497133 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1203013391 / 1000000000000 : ℚ) +
        (2705529897 / 250000000000000000 : ℚ) / (2289219999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (287887901 / 200000000000 : ℚ) + (1813816411 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8320497133 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12050]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12050 :
    2 * 160 < 12050 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997161 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12050 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12051 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12051. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12051 : WorldParameters where
  hiddenCharge := (1202961357 / 1000000000000 : ℝ)
  frame := (31755312649 / 50000000000 : ℝ)
  moment := (1352470991 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12051 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (376329138193 / 250000000000 : ℝ)
    root := (3782794939 / 500000000000 : ℝ) }

noncomputable def scalar12051 : ScalarCertificate 12051 world12051 agent12051 where
  dimensionLo := 12051
  dimensionHi := 12051
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2289621899 / 1000000000000 : ℝ)
  frameLo := (31755312649 / 50000000000 : ℝ)
  frameHi := (376329138193 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12051]
  agentFrame_pos := by norm_num only [agent12051]
  worldRadius := (2289621899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12051]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (179766511 / 125000000000 : ℝ)
  lowerTail := (226536117 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8316436713 / 1000000000000 : ℝ)
  ledger := by
    have h : (1202961357 / 1000000000000 : ℚ) +
        (1352470991 / 125000000000000000 : ℚ) / (2289621899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (179766511 / 125000000000 : ℚ) + (226536117 / 125000000000 : ℚ) ≤
        (8316436713 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1202961357 / 1000000000000 : ℚ) +
        (1352470991 / 125000000000000000 : ℚ) / (2289621899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (179766511 / 125000000000 : ℚ) + (226536117 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8316436713 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12051]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12051 :
    2 * 160 < 12051 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999633 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12051 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12052 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12052. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12052 : WorldParameters where
  hiddenCharge := (601454669 / 500000000000 : ℝ)
  frame := (635090839933 / 1000000000000 : ℝ)
  moment := (5408708491 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12052 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1505265824927 / 1000000000000 : ℝ)
    root := (7564896571 / 1000000000000 : ℝ) }

noncomputable def scalar12052 : ScalarCertificate 12052 world12052 agent12052 where
  dimensionLo := 12052
  dimensionHi := 12052
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2290023699 / 1000000000000 : ℝ)
  frameLo := (635090839933 / 1000000000000 : ℝ)
  frameHi := (1505265824927 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12052]
  agentFrame_pos := by norm_num only [agent12052]
  worldRadius := (2290023699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12052]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (359206519 / 250000000000 : ℝ)
  lowerTail := (181076301 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8312380271 / 1000000000000 : ℝ)
  ledger := by
    have h : (601454669 / 500000000000 : ℚ) +
        (5408708491 / 500000000000000000 : ℚ) / (2290023699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (359206519 / 250000000000 : ℚ) + (181076301 / 100000000000 : ℚ) ≤
        (8312380271 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((601454669 / 500000000000 : ℚ) +
        (5408708491 / 500000000000000000 : ℚ) / (2290023699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (359206519 / 250000000000 : ℚ) + (181076301 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8312380271 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12052]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12052 :
    2 * 160 < 12052 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994743 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12052 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12053 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12053. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12053 : WorldParameters where
  hiddenCharge := (1202857333 / 1000000000000 : ℝ)
  frame := (317537714761 / 500000000000 : ℝ)
  moment := (10815066749 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12053 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (47037964199 / 31250000000 : ℝ)
    root := (3782101707 / 500000000000 : ℝ) }

noncomputable def scalar12053 : ScalarCertificate 12053 world12053 agent12053 where
  dimensionLo := 12053
  dimensionHi := 12053
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2290425899 / 1000000000000 : ℝ)
  frameLo := (317537714761 / 500000000000 : ℝ)
  frameHi := (47037964199 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12053]
  agentFrame_pos := by norm_num only [agent12053]
  worldRadius := (2290425899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12053]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1435520553 / 1000000000000 : ℝ)
  lowerTail := (452309351 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2077081191 / 250000000000 : ℝ)
  ledger := by
    have h : (1202857333 / 1000000000000 : ℚ) +
        (10815066749 / 1000000000000000000 : ℚ) / (2290425899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1435520553 / 1000000000000 : ℚ) + (452309351 / 250000000000 : ℚ) ≤
        (2077081191 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1202857333 / 1000000000000 : ℚ) +
        (10815066749 / 1000000000000000000 : ℚ) / (2290425899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1435520553 / 1000000000000 : ℚ) + (452309351 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2077081191 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12053]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12053 :
    2 * 160 < 12053 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (109999969 / 10000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12053 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12054 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12054. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12054 : WorldParameters where
  hiddenCharge := (1202805343 / 1000000000000 : ℝ)
  frame := (317530010873 / 500000000000 : ℝ)
  moment := (1081271723 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12054 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1505163829653 / 1000000000000 : ℝ)
    root := (1890877621 / 250000000000 : ℝ) }

noncomputable def scalar12054 : ScalarCertificate 12054 world12054 agent12054 where
  dimensionLo := 12054
  dimensionHi := 12054
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2290828199 / 1000000000000 : ℝ)
  frameLo := (317530010873 / 500000000000 : ℝ)
  frameHi := (1505163829653 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12054]
  agentFrame_pos := by norm_num only [agent12054]
  worldRadius := (2290828199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12054]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1434216143 / 1000000000000 : ℝ)
  lowerTail := (451928239 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8304272197 / 1000000000000 : ℝ)
  ledger := by
    have h : (1202805343 / 1000000000000 : ℚ) +
        (1081271723 / 100000000000000000 : ℚ) / (2290828199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1434216143 / 1000000000000 : ℚ) + (451928239 / 250000000000 : ℚ) ≤
        (8304272197 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1202805343 / 1000000000000 : ℚ) +
        (1081271723 / 100000000000000000 : ℚ) / (2290828199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1434216143 / 1000000000000 : ℚ) + (451928239 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8304272197 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12054]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12054 :
    2 * 160 < 12054 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995261 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12054 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12055 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12055. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12055 : WorldParameters where
  hiddenCharge := (1202753367 / 1000000000000 : ℝ)
  frame := (158761154151 / 250000000000 : ℝ)
  moment := (10810368423 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12055 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1505112829837 / 1000000000000 : ℝ)
    root := (7562817859 / 1000000000000 : ℝ) }

noncomputable def scalar12055 : ScalarCertificate 12055 world12055 agent12055 where
  dimensionLo := 12055
  dimensionHi := 12055
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2291230599 / 1000000000000 : ℝ)
  frameLo := (158761154151 / 250000000000 : ℝ)
  frameHi := (1505112829837 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12055]
  agentFrame_pos := by norm_num only [agent12055]
  worldRadius := (2291230599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12055]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1432913249 / 1000000000000 : ℝ)
  lowerTail := (903095089 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8300223481 / 1000000000000 : ℝ)
  ledger := by
    have h : (1202753367 / 1000000000000 : ℚ) +
        (10810368423 / 1000000000000000000 : ℚ) / (2291230599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1432913249 / 1000000000000 : ℚ) + (903095089 / 500000000000 : ℚ) ≤
        (8300223481 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1202753367 / 1000000000000 : ℚ) +
        (10810368423 / 1000000000000000000 : ℚ) / (2291230599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1432913249 / 1000000000000 : ℚ) + (903095089 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8300223481 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12055]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12055 :
    2 * 160 < 12055 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999789 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12055 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12056 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12056. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12056 : WorldParameters where
  hiddenCharge := (601350703 / 500000000000 : ℝ)
  frame := (635029214097 / 1000000000000 : ℝ)
  moment := (1080802033 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12056 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1505061867061 / 1000000000000 : ℝ)
    root := (945265673 / 125000000000 : ℝ) }

noncomputable def scalar12056 : ScalarCertificate 12056 world12056 agent12056 where
  dimensionLo := 12056
  dimensionHi := 12056
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2291632999 / 1000000000000 : ℝ)
  frameLo := (635029214097 / 1000000000000 : ℝ)
  frameHi := (1505061867061 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12056]
  agentFrame_pos := by norm_num only [agent12056]
  worldRadius := (2291632999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12056]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (143161171 / 100000000000 : ℝ)
  lowerTail := (1804668903 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (829617847 / 100000000000 : ℝ)
  ledger := by
    have h : (601350703 / 500000000000 : ℚ) +
        (1080802033 / 100000000000000000 : ℚ) / (2291632999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (143161171 / 100000000000 : ℚ) + (1804668903 / 1000000000000 : ℚ) ≤
        (829617847 / 100000000000 : ℚ) := by norm_num only
    have hc : (((601350703 / 500000000000 : ℚ) +
        (1080802033 / 100000000000000000 : ℚ) / (2291632999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (143161171 / 100000000000 : ℚ) + (1804668903 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((829617847 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12056]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12056 :
    2 * 160 < 12056 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998389 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12056 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12057 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12057. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12057 : WorldParameters where
  hiddenCharge := (1202649459 / 1000000000000 : ℝ)
  frame := (317506907111 / 500000000000 : ℝ)
  moment := (2701418237 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12057 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (752505464569 / 500000000000 : ℝ)
    root := (1512286627 / 200000000000 : ℝ) }

noncomputable def scalar12057 : ScalarCertificate 12057 world12057 agent12057 where
  dimensionLo := 12057
  dimensionHi := 12057
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2292035299 / 1000000000000 : ℝ)
  frameLo := (317506907111 / 500000000000 : ℝ)
  frameHi := (752505464569 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12057]
  agentFrame_pos := by norm_num only [agent12057]
  worldRadius := (2292035299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12057]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1430311453 / 1000000000000 : ℝ)
  lowerTail := (1803149033 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8292137169 / 1000000000000 : ℝ)
  ledger := by
    have h : (1202649459 / 1000000000000 : ℚ) +
        (2701418237 / 250000000000000000 : ℚ) / (2292035299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1430311453 / 1000000000000 : ℚ) + (1803149033 / 1000000000000 : ℚ) ≤
        (8292137169 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1202649459 / 1000000000000 : ℚ) +
        (2701418237 / 250000000000000000 : ℚ) / (2292035299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1430311453 / 1000000000000 : ℚ) + (1803149033 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8292137169 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12057]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12057 :
    2 * 160 < 12057 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999969 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12057 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12058 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12058. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12058 : WorldParameters where
  hiddenCharge := (1202597527 / 1000000000000 : ℝ)
  frame := (634998416979 / 1000000000000 : ℝ)
  moment := (270083157 / 25000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12058 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1504960028211 / 1000000000000 : ℝ)
    root := (3780370557 / 500000000000 : ℝ) }

noncomputable def scalar12058 : ScalarCertificate 12058 world12058 agent12058 where
  dimensionLo := 12058
  dimensionHi := 12058
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2292437699 / 1000000000000 : ℝ)
  frameLo := (634998416979 / 1000000000000 : ℝ)
  frameHi := (1504960028211 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12058]
  agentFrame_pos := by norm_num only [agent12058]
  worldRadius := (2292437699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12058]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (285802539 / 200000000000 : ℝ)
  lowerTail := (1801630827 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4144049849 / 500000000000 : ℝ)
  ledger := by
    have h : (1202597527 / 1000000000000 : ℚ) +
        (270083157 / 25000000000000000 : ℚ) / (2292437699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (285802539 / 200000000000 : ℚ) + (1801630827 / 1000000000000 : ℚ) ≤
        (4144049849 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1202597527 / 1000000000000 : ℚ) +
        (270083157 / 25000000000000000 : ℚ) / (2292437699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (285802539 / 200000000000 : ℚ) + (1801630827 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4144049849 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12058]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12058 :
    2 * 160 < 12058 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998317 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12058 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding12034 :
    (1203847914238185024437 / 1000000000000000000000000 : ℝ) ≤ world12034.hiddenCharge ∧
    (635368678759049380811563 / 1000000000000000000000000 : ℝ) ≤ world12034.frame ∧
    (2171968693496917 / 200000000000000000000000 : ℝ) ≤ world12034.moment ∧
    (376545894969077368986701 / 250000000000000000000000 : ℝ) ≤ agent12034.frame ∧
    (7577411923333127731429 / 1000000000000000000000000 : ℝ) ≤ agent12034.root ∧
    scalar12034.worldRadius ≤ (2282790599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (656916267974309104101 / 500000000000000000000000 : ℝ) ≤ agent12034.charge ∧
    (1460549314924332762519 / 1000000000000000000000000 : ℝ) ≤ scalar12034.upperTail ∧
    (919233314208341327441 / 500000000000000000000000 : ℝ) ≤ scalar12034.lowerTail ∧
    scalar12034.totalBudget ≤ (4192989811570932493331 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12034, agent12034, scalar12034] <;> simp only [true_and]

theorem source_rounding12035 :
    (1203795646959234008537 / 1000000000000000000000000 : ℝ) ≤ world12035.hiddenCharge ∧
    (635353220792518002093399 / 1000000000000000000000000 : ℝ) ≤ world12035.frame ∧
    (1357185043396651 / 125000000000000000000000 : ℝ) ≤ world12035.moment ∧
    (94133271251115291262707 / 62500000000000000000000 : ℝ) ≤ agent12035.frame ∧
    (757671464573835646077 / 100000000000000000000000 : ℝ) ≤ agent12035.root ∧
    scalar12035.worldRadius ≤ (2283192499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1313466563920377664253 / 1000000000000000000000000 : ℝ) ≤ agent12035.charge ∧
    (91201211947810118269 / 62500000000000000000000 : ℝ) ≤ scalar12035.upperTail ∧
    (367382872488850618533 / 200000000000000000000000 : ℝ) ≤ scalar12035.lowerTail ∧
    scalar12035.totalBudget ≤ (1676371650100857991137 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12035, agent12035, scalar12035] <;> simp only [true_and]

theorem source_rounding12036 :
    (1203743394310406532219 / 1000000000000000000000000 : ℝ) ≤ world12036.hiddenCharge ∧
    (635337765474091645315043 / 1000000000000000000000000 : ℝ) ≤ world12036.frame ∧
    (10855117945212399 / 1000000000000000000000000 : ℝ) ≤ world12036.moment ∧
    (1506081125444564522536887 / 1000000000000000000000000 : ℝ) ≤ agent12036.frame ∧
    (7576017676542350300283 / 1000000000000000000000000 : ℝ) ≤ agent12036.root ∧
    scalar12036.worldRadius ≤ (2283594299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (656550527917391567997 / 500000000000000000000000 : ℝ) ≤ agent12036.charge ∧
    (291578169610511084667 / 200000000000000000000000 : ℝ) ≤ scalar12036.upperTail ∧
    (1835363605355272965059 / 1000000000000000000000000 : ℝ) ≤ scalar12036.lowerTail ∧
    scalar12036.totalBudget ≤ (837774080942103117599 / 100000000000000000000000 : ℝ) := by
  norm_num only [world12036, agent12036, scalar12036] <;> simp only [true_and]

theorem source_rounding12037 :
    (300922789071585732749 / 250000000000000000000000 : ℝ) ≤ world12037.hiddenCharge ∧
    (635322312803047393257613 / 1000000000000000000000000 : ℝ) ≤ world12037.frame ∧
    (10852756261321893 / 1000000000000000000000000 : ℝ) ≤ world12037.moment ∧
    (47063435694421604827319 / 31250000000000000000000 : ℝ) ≤ agent12037.frame ∧
    (7575320859241783849227 / 1000000000000000000000000 : ℝ) ≤ agent12037.root ∧
    scalar12037.worldRadius ≤ (2283996099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (262547202197725365501 / 200000000000000000000000 : ℝ) ≤ agent12037.charge ∧
    (1456563664539056408237 / 1000000000000000000000000 : ℝ) ≤ scalar12037.upperTail ∧
    (1833814349162220022627 / 1000000000000000000000000 : ℝ) ≤ scalar12037.lowerTail ∧
    scalar12037.totalBudget ≤ (8373627086843050593139 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12037, agent12037, scalar12037] <;> simp only [true_and]

theorem source_rounding12038 :
    (1203638932881688878081 / 1000000000000000000000000 : ℝ) ≤ world12038.hiddenCharge ∧
    (635306862778662506963181 / 1000000000000000000000000 : ℝ) ≤ world12038.frame ∧
    (10850395295221677 / 1000000000000000000000000 : ℝ) ≤ world12038.moment ∧
    (301195758065174831957751 / 200000000000000000000000 : ℝ) ≤ agent12038.frame ∧
    (3787312135931018362257 / 500000000000000000000000 : ℝ) ≤ agent12038.root ∧
    scalar12038.worldRadius ≤ (2284397899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (65618571433996369791 / 50000000000000000000000 : ℝ) ≤ agent12038.charge ∧
    (1455237904101606919137 / 1000000000000000000000000 : ℝ) ≤ scalar12038.upperTail ∧
    (1832266661380771045923 / 1000000000000000000000000 : ℝ) ≤ scalar12038.lowerTail ∧
    scalar12038.totalBudget ≤ (8369517213332577508987 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12038, agent12038, scalar12038] <;> simp only [true_and]

theorem source_rounding12039 :
    (120358672409108972657 / 100000000000000000000000 : ℝ) ≤ world12039.hiddenCharge ∧
    (158822853850053619101799 / 250000000000000000000000 : ℝ) ≤ world12039.frame ∧
    (10848035046631759 / 1000000000000000000000000 : ℝ) ≤ world12039.moment ∧
    (1505927669734990373345257 / 1000000000000000000000000 : ℝ) ≤ agent12039.frame ∧
    (3786963996181418740987 / 500000000000000000000000 : ℝ) ≤ agent12039.root ∧
    scalar12039.worldRadius ≤ (2284799799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1312007308207927570743 / 1000000000000000000000000 : ℝ) ≤ agent12039.charge ∧
    (290782742852617291721 / 200000000000000000000000 : ℝ) ≤ scalar12039.upperTail ∧
    (1830720706870589894243 / 1000000000000000000000000 : ℝ) ≤ scalar12039.lowerTail ∧
    scalar12039.totalBudget ≤ (4182705658970922339531 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12039, agent12039, scalar12039] <;> simp only [true_and]

theorem source_rounding12040 :
    (1203534529909197573159 / 1000000000000000000000000 : ℝ) ≤ world12040.hiddenCharge ∧
    (127055194133396252746501 / 200000000000000000000000 : ℝ) ≤ world12040.frame ∧
    (1355709439409057 / 125000000000000000000000 : ℝ) ≤ world12040.moment ∧
    (1505876580426145824753377 / 1000000000000000000000000 : ℝ) ≤ agent12040.frame ∧
    (946653983042502068551 / 125000000000000000000000 : ℝ) ≤ agent12040.root ∧
    scalar12040.worldRadius ≤ (2285201699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (262328729774618355933 / 200000000000000000000000 : ℝ) ≤ agent12040.charge ∧
    (726295439369632187809 / 500000000000000000000000 : ℝ) ≤ scalar12040.upperTail ∧
    (914588123840784789157 / 500000000000000000000000 : ℝ) ≤ scalar12040.lowerTail ∧
    scalar12040.totalBudget ≤ (8361309127182479994549 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12040, agent12040, scalar12040] <;> simp only [true_and]

theorem source_rounding12041 :
    (601741175165329979217 / 500000000000000000000000 : ℝ) ≤ world12041.hiddenCharge ∧
    (635260528578240896386093 / 1000000000000000000000000 : ℝ) ≤ world12041.frame ∧
    (2168663340172787 / 200000000000000000000000 : ℝ) ≤ world12041.moment ∧
    (301165103258177663602543 / 200000000000000000000000 : ℝ) ≤ agent12041.frame ∧
    (1514507208770630928199 / 200000000000000000000000 : ℝ) ≤ agent12041.root ∧
    scalar12041.worldRadius ≤ (2285603399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (327820112494275944347 / 250000000000000000000000 : ℝ) ≤ agent12041.charge ∧
    (1451269330934933750393 / 1000000000000000000000000 : ℝ) ≤ scalar12041.upperTail ∧
    (1827633190734827992651 / 1000000000000000000000000 : ℝ) ≤ scalar12041.lowerTail ∧
    scalar12041.totalBudget ≤ (8357210845216825199363 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12041, agent12041, scalar12041] <;> simp only [true_and]

theorem source_rounding12042 :
    (1203430185350135395841 / 1000000000000000000000000 : ℝ) ≤ world12042.hiddenCharge ∧
    (635245089133271737007617 / 1000000000000000000000000 : ℝ) ≤ world12042.frame ∧
    (5420479301563421 / 500000000000000000000000 : ℝ) ≤ world12042.moment ∧
    (150577448947844030388979 / 100000000000000000000000 : ℝ) ≤ agent12042.frame ∧
    (3785920187282024838543 / 500000000000000000000000 : ℝ) ≤ agent12042.root ∧
    scalar12042.worldRadius ≤ (2286005299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (163864713852858035117 / 125000000000000000000000 : ℝ) ≤ agent12042.charge ∧
    (1449949328936099371059 / 1000000000000000000000000 : ℝ) ≤ scalar12042.upperTail ∧
    (1826091855079626765101 / 1000000000000000000000000 : ℝ) ≤ scalar12042.lowerTail ∧
    scalar12042.totalBudget ≤ (522069770060210624497 / 62500000000000000000000 : ℝ) := by
  norm_num only [world12042, agent12042, scalar12042] <;> simp only [true_and]

theorem source_rounding12043 :
    (240675606992455286837 / 200000000000000000000000 : ℝ) ≤ world12043.hiddenCharge ∧
    (635229652331352472956581 / 1000000000000000000000000 : ℝ) ≤ world12043.frame ∧
    (10838601221781619 / 1000000000000000000000000 : ℝ) ≤ world12043.moment ∧
    (376430871948726666055413 / 250000000000000000000000 : ℝ) ≤ agent12043.frame ∧
    (1892786233604183372731 / 250000000000000000000000 : ℝ) ≤ agent12043.root ∧
    scalar12043.worldRadius ≤ (2286407099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (655277715357244304669 / 500000000000000000000000 : ℝ) ≤ agent12043.charge ∧
    (1448630630580456390827 / 1000000000000000000000000 : ℝ) ≤ scalar12043.upperTail ∧
    (1824551946573822477563 / 1000000000000000000000000 : ℝ) ≤ scalar12043.lowerTail ∧
    scalar12043.totalBudget ≤ (8349025562589173898191 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12043, agent12043, scalar12043] <;> simp only [true_and]

theorem source_rounding12044 :
    (601662949580871883011 / 500000000000000000000000 : ℝ) ≤ world12044.hiddenCharge ∧
    (317607109085880962029019 / 500000000000000000000000 : ℝ) ≤ world12044.frame ∧
    (10836244556549069 / 1000000000000000000000000 : ℝ) ≤ world12044.moment ∧
    (752836258651746138533927 / 500000000000000000000000 : ℝ) ≤ agent12044.frame ∧
    (3785224900644849290149 / 500000000000000000000000 : ℝ) ≤ agent12044.root ∧
    scalar12044.worldRadius ≤ (2286808999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1310193608957304328379 / 1000000000000000000000000 : ℝ) ≤ agent12044.charge ∧
    (1447313493342372067537 / 1000000000000000000000000 : ℝ) ≤ scalar12044.upperTail ∧
    (911506880689429492293 / 500000000000000000000000 : ℝ) ≤ scalar12044.lowerTail ∧
    scalar12044.totalBudget ≤ (4172469380227462457577 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12044, agent12044, scalar12044] <;> simp only [true_and]

theorem source_rounding12045 :
    (9400576390181232523 / 7812500000000000000000 : ℝ) ≤ world12045.hiddenCharge ∧
    (39699924165861206677683 / 62500000000000000000000 : ℝ) ≤ world12045.frame ∧
    (10833888607150021 / 1000000000000000000000000 : ℝ) ≤ world12045.moment ∧
    (1505621577981643850567159 / 1000000000000000000000000 : ℝ) ≤ agent12045.frame ∧
    (7569754818943726275661 / 1000000000000000000000000 : ℝ) ≤ agent12045.root ∧
    scalar12045.worldRadius ≤ (2287210799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (327458061214462225077 / 250000000000000000000000 : ℝ) ≤ agent12045.charge ∧
    (144599761801783756821 / 100000000000000000000000 : ℝ) ≤ scalar12045.upperTail ∧
    (1821476965364621346661 / 1000000000000000000000000 : ℝ) ≤ scalar12045.lowerTail ∧
    scalar12045.totalBudget ≤ (2085213910598813827419 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12045, agent12045, scalar12045] <;> simp only [true_and]

theorem source_rounding12046 :
    (601610835650651351811 / 500000000000000000000000 : ℝ) ≤ world12046.hiddenCharge ∧
    (317591678888342028778521 / 500000000000000000000000 : ℝ) ≤ world12046.frame ∧
    (2166306674661099 / 200000000000000000000000 : ℝ) ≤ world12046.moment ∧
    (752785331861242078231977 / 500000000000000000000000 : ℝ) ≤ agent12046.frame ∧
    (1892265035818783442507 / 250000000000000000000000 : ℝ) ≤ agent12046.root ∧
    scalar12046.worldRadius ≤ (2287612699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1309471337723867338483 / 1000000000000000000000000 : ℝ) ≤ agent12046.charge ∧
    (1444683273705049653597 / 1000000000000000000000000 : ℝ) ≤ scalar12046.upperTail ∧
    (363988370861046347701 / 200000000000000000000000 : ℝ) ≤ scalar12046.lowerTail ∧
    scalar12046.totalBudget ≤ (333471056422049673021 / 40000000000000000000000 : ℝ) := by
  norm_num only [world12046, agent12046, scalar12046] <;> simp only [true_and]

theorem source_rounding12047 :
    (240633915846145072399 / 200000000000000000000000 : ℝ) ≤ world12047.hiddenCharge ∧
    (635167931539755920442351 / 1000000000000000000000000 : ℝ) ≤ world12047.frame ∧
    (10829178854736647 / 1000000000000000000000000 : ℝ) ≤ world12047.moment ∧
    (376379945147110247944377 / 250000000000000000000000 : ℝ) ≤ agent12047.frame ∧
    (7568365618110555215191 / 1000000000000000000000000 : ℝ) ≤ agent12047.root ∧
    scalar12047.worldRadius ≤ (2288014499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (654555443432154933481 / 500000000000000000000000 : ℝ) ≤ agent12047.charge ∧
    (1443370188081815827819 / 1000000000000000000000000 : ℝ) ≤ scalar12047.upperTail ∧
    (909204064514889202263 / 500000000000000000000000 : ℝ) ≤ scalar12047.lowerTail ∧
    scalar12047.totalBudget ≤ (208317521351571958349 / 25000000000000000000000 : ℝ) := by
  norm_num only [world12047, agent12047, scalar12047] <;> simp only [true_and]

theorem source_rounding12048 :
    (601558750863066096677 / 500000000000000000000000 : ℝ) ≤ world12048.hiddenCharge ∧
    (15878812698556870736511 / 25000000000000000000000 : ℝ) ≤ world12048.frame ∧
    (2165365010232931 / 200000000000000000000000 : ℝ) ≤ world12048.moment ∧
    (47045904207525766695009 / 31250000000000000000000 : ℝ) ≤ agent12048.frame ∧
    (756767132131281004809 / 100000000000000000000000 : ℝ) ≤ agent12048.root ∧
    scalar12048.worldRadius ≤ (2288416399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1308750891589329584993 / 1000000000000000000000000 : ℝ) ≤ agent12048.charge ∧
    (1442058617898308107431 / 1000000000000000000000000 : ℝ) ≤ scalar12048.upperTail ∧
    (90843804245913865797 / 50000000000000000000000 : ℝ) ≤ scalar12048.lowerTail ∧
    scalar12048.totalBudget ≤ (8328629164872001780557 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12048, agent12048, scalar12048] <;> simp only [true_and]

theorem source_rounding12049 :
    (48122617551287854691 / 40000000000000000000000 : ℝ) ≤ world12049.hiddenCharge ∧
    (635137086983521059047751 / 1000000000000000000000000 : ℝ) ≤ world12049.frame ∧
    (2164894392462201 / 200000000000000000000000 : ℝ) ≤ world12049.moment ∧
    (752709053802927327638233 / 500000000000000000000000 : ℝ) ≤ agent12049.frame ∧
    (7566977330679289835553 / 1000000000000000000000000 : ℝ) ≤ agent12049.root ∧
    scalar12049.worldRadius ≤ (2288818199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (81774459450642508527 / 62500000000000000000000 : ℝ) ≤ agent12049.charge ∧
    (90046773715561355071 / 62500000000000000000000 : ℝ) ≤ scalar12049.upperTail ∧
    (907672745815402086721 / 500000000000000000000000 : ℝ) ≤ scalar12049.lowerTail ∧
    scalar12049.totalBudget ≤ (4162280643515767199519 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12049, agent12049, scalar12049] <;> simp only [true_and]

theorem source_rounding12050 :
    (1203013390393590731679 / 1000000000000000000000000 : ℝ) ≤ world12050.hiddenCharge ∧
    (317560834331387536213217 / 500000000000000000000000 : ℝ) ≤ world12050.frame ∧
    (10822119587897203 / 1000000000000000000000000 : ℝ) ≤ world12050.moment ∧
    (752683658856228413142981 / 500000000000000000000000 : ℝ) ≤ agent12050.frame ∧
    (945785436266930019137 / 125000000000000000000000 : ℝ) ≤ agent12050.root ∧
    scalar12050.worldRadius ≤ (2289219999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (65401613251985669203 / 50000000000000000000000 : ℝ) ≤ agent12050.charge ∧
    (1439439504794479226427 / 1000000000000000000000000 : ℝ) ≤ scalar12050.upperTail ∧
    (453454102568466213667 / 250000000000000000000000 : ℝ) ≤ scalar12050.lowerTail ∧
    scalar12050.totalBudget ≤ (104006214168501977847 / 12500000000000000000000 : ℝ) := by
  norm_num only [world12050, agent12050, scalar12050] <;> simp only [true_and]

theorem source_rounding12051 :
    (1202961356554989222309 / 1000000000000000000000000 : ℝ) ≤ world12051.hiddenCharge ∧
    (127021250595863536069257 / 200000000000000000000000 : ℝ) ≤ world12051.frame ∧
    (10819767927644837 / 1000000000000000000000000 : ℝ) ≤ world12051.moment ∧
    (376329138192886000085279 / 250000000000000000000000 : ℝ) ≤ agent12051.frame ∧
    (7565589877495394265651 / 1000000000000000000000000 : ℝ) ≤ agent12051.root ∧
    scalar12051.worldRadius ≤ (2289621899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1307673632391377088773 / 1000000000000000000000000 : ℝ) ≤ agent12051.charge ∧
    (719066043817815085213 / 500000000000000000000000 : ℝ) ≤ scalar12051.upperTail ∧
    (1812288935763140986841 / 1000000000000000000000000 : ℝ) ≤ scalar12051.lowerTail ∧
    scalar12051.totalBudget ≤ (4158218356572586139881 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12051, agent12051, scalar12051] <;> simp only [true_and]

theorem source_rounding12052 :
    (601454668630536239271 / 500000000000000000000000 : ℝ) ≤ world12052.hiddenCharge ∧
    (317545419966215003396193 / 500000000000000000000000 : ℝ) ≤ world12052.frame ∧
    (5408708490637899 / 500000000000000000000000 : ℝ) ≤ world12052.moment ∧
    (301053164985377708724151 / 200000000000000000000000 : ℝ) ≤ agent12052.frame ∧
    (3782448285253962177871 / 500000000000000000000000 : ℝ) ≤ agent12052.root ∧
    scalar12052.worldRadius ≤ (2290023699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (326828863145053148417 / 250000000000000000000000 : ℝ) ≤ agent12052.charge ∧
    (718413037872548610037 / 500000000000000000000000 : ℝ) ≤ scalar12052.upperTail ∧
    (1810763009473519550799 / 1000000000000000000000000 : ℝ) ≤ scalar12052.lowerTail ∧
    scalar12052.totalBudget ≤ (207809506786806044461 / 25000000000000000000000 : ℝ) := by
  norm_num only [world12052, agent12052, scalar12052] <;> simp only [true_and]

theorem source_rounding12053 :
    (1202857332506518012093 / 1000000000000000000000000 : ℝ) ≤ world12053.hiddenCharge ∧
    (635075429521393220751387 / 1000000000000000000000000 : ℝ) ≤ world12053.frame ∧
    (10815066748511887 / 1000000000000000000000000 : ℝ) ≤ world12053.moment ∧
    (1505214854367189121038339 / 1000000000000000000000000 : ℝ) ≤ agent12053.frame ∧
    (7564203413197184385089 / 1000000000000000000000000 : ℝ) ≤ agent12053.root ∧
    scalar12053.worldRadius ≤ (2290425899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1306957724922352512979 / 1000000000000000000000000 : ℝ) ≤ agent12053.charge ∧
    (179440069017617183279 / 125000000000000000000000 : ℝ) ≤ scalar12053.upperTail ∧
    (180923740308691837841 / 100000000000000000000000 : ℝ) ≤ scalar12053.lowerTail ∧
    scalar12053.totalBudget ≤ (4154162382139338399271 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12053, agent12053, scalar12053] <;> simp only [true_and]

theorem source_rounding12054 :
    (601402671143005718031 / 500000000000000000000000 : ℝ) ≤ world12054.hiddenCharge ∧
    (635060021745489059142271 / 1000000000000000000000000 : ℝ) ≤ world12054.frame ∧
    (2703179307268817 / 250000000000000000000000 : ℝ) ≤ world12054.moment ∧
    (188145478706600377972807 / 125000000000000000000000 : ℝ) ≤ agent12054.frame ∧
    (1512702096665734013033 / 200000000000000000000000 : ℝ) ≤ agent12054.root ∧
    scalar12054.worldRadius ≤ (2290828199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1306600448735118425881 / 1000000000000000000000000 : ℝ) ≤ agent12054.charge ∧
    (717108071014146069643 / 500000000000000000000000 : ℝ) ≤ scalar12054.upperTail ∧
    (1807712955323051199417 / 1000000000000000000000000 : ℝ) ≤ scalar12054.lowerTail ∧
    scalar12054.totalBudget ≤ (4152136098670836549581 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12054, agent12054, scalar12054] <;> simp only [true_and]

theorem source_rounding12055 :
    (120275336659423804121 / 100000000000000000000000 : ℝ) ≤ world12055.hiddenCharge ∧
    (635044616603999313089163 / 1000000000000000000000000 : ℝ) ≤ world12055.frame ∧
    (17296589476301 / 1600000000000000000000 : ℝ) ≤ world12055.moment ∧
    (1505112829836569179943367 / 1000000000000000000000000 : ℝ) ≤ agent12055.frame ∧
    (7562817858602582720099 / 1000000000000000000000000 : ℝ) ≤ agent12055.root ∧
    scalar12055.worldRadius ≤ (2291230599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1306243623337018575129 / 1000000000000000000000000 : ℝ) ≤ agent12055.charge ∧
    (1432913248005232704097 / 1000000000000000000000000 : ℝ) ≤ scalar12055.upperTail ∧
    (903095088609968461479 / 500000000000000000000000 : ℝ) ≤ scalar12055.lowerTail ∧
    scalar12055.totalBudget ≤ (2075055870324870928217 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12055, agent12055, scalar12055] <;> simp only [true_and]

theorem source_rounding12056 :
    (601350702712941400627 / 500000000000000000000000 : ℝ) ≤ world12056.hiddenCharge ∧
    (635029214096206039124499 / 1000000000000000000000000 : ℝ) ≤ world12056.frame ∧
    (10808020329072667 / 1000000000000000000000000 : ℝ) ≤ world12056.moment ∧
    (1505061867060043741152829 / 1000000000000000000000000 : ℝ) ≤ agent12056.frame ∧
    (7562125383141681812627 / 1000000000000000000000000 : ℝ) ≤ agent12056.root ∧
    scalar12056.worldRadius ≤ (2291632999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (65294362402387278527 / 50000000000000000000000 : ℝ) ≤ agent12056.charge ∧
    (178951463650968675327 / 125000000000000000000000 : ℝ) ≤ scalar12056.upperTail ∧
    (1804668902339098336647 / 1000000000000000000000000 : ℝ) ≤ scalar12056.lowerTail ∧
    scalar12056.totalBudget ≤ (8296178470467322056269 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12056, agent12056, scalar12056] <;> simp only [true_and]

theorem source_rounding12057 :
    (300662364693909694661 / 250000000000000000000000 : ℝ) ≤ world12057.hiddenCharge ∧
    (79376726777673960647519 / 125000000000000000000000 : ℝ) ≤ world12057.frame ∧
    (5402836473975731 / 500000000000000000000000 : ℝ) ≤ world12057.moment ∧
    (1505010929137716837644113 / 1000000000000000000000000 : ℝ) ≤ agent12057.frame ∧
    (7561433134662874056561 / 1000000000000000000000000 : ℝ) ≤ agent12057.root ∧
    scalar12057.worldRadius ≤ (2292035299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (652765661094087048643 / 500000000000000000000000 : ℝ) ≤ agent12057.charge ∧
    (715155726288154340571 / 500000000000000000000000 : ℝ) ≤ scalar12057.upperTail ∧
    (1803149032398057364053 / 1000000000000000000000000 : ℝ) ≤ scalar12057.lowerTail ∧
    scalar12057.totalBudget ≤ (8292137169587836039529 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12057, agent12057, scalar12057] <;> simp only [true_and]

theorem source_rounding12058 :
    (1202597526638197313673 / 1000000000000000000000000 : ℝ) ≤ world12058.hiddenCharge ∧
    (634998416978838922822993 / 1000000000000000000000000 : ℝ) ≤ world12058.frame ∧
    (5401663139523523 / 500000000000000000000000 : ℝ) ≤ world12058.moment ∧
    (23515000440782025162257 / 15625000000000000000000 : ℝ) ≤ agent12058.frame ∧
    (7560741113013100333999 / 1000000000000000000000000 : ℝ) ≤ agent12058.root ∧
    scalar12058.worldRadius ≤ (2292437699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1305175845080358629011 / 1000000000000000000000000 : ℝ) ≤ agent12058.charge ∧
    (1429012694886592795681 / 1000000000000000000000000 : ℝ) ≤ scalar12058.upperTail ∧
    (1801630826572816303289 / 1000000000000000000000000 : ℝ) ≤ scalar12058.lowerTail ∧
    scalar12058.totalBudget ≤ (8288099698123522543767 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12058, agent12058, scalar12058] <;> simp only [true_and]

noncomputable def paperAgent12034 : AgentParameters :=
  { agent12034 with charge := (1313832539 / 1000000000000 : ℝ) }

theorem agent_is_repriced12034 : agent12034 =
    BstLean.Part265.agentRepriced 12034 world12034 paperAgent12034 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12034, agent12034]

noncomputable def paperAgent12035 : AgentParameters :=
  { agent12035 with charge := (164183321 / 125000000000 : ℝ) }

theorem agent_is_repriced12035 : agent12035 =
    BstLean.Part265.agentRepriced 12035 world12035 paperAgent12035 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12035, agent12035]

noncomputable def paperAgent12036 : AgentParameters :=
  { agent12036 with charge := (65655053 / 50000000000 : ℝ) }

theorem agent_is_repriced12036 : agent12036 =
    BstLean.Part265.agentRepriced 12036 world12036 paperAgent12036 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12036, agent12036]

noncomputable def paperAgent12037 : AgentParameters :=
  { agent12037 with charge := (262547203 / 200000000000 : ℝ) }

theorem agent_is_repriced12037 : agent12037 =
    BstLean.Part265.agentRepriced 12037 world12037 paperAgent12037 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12037, agent12037]

noncomputable def paperAgent12038 : AgentParameters :=
  { agent12038 with charge := (164046429 / 125000000000 : ℝ) }

theorem agent_is_repriced12038 : agent12038 =
    BstLean.Part265.agentRepriced 12038 world12038 paperAgent12038 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12038, agent12038]

noncomputable def paperAgent12039 : AgentParameters :=
  { agent12039 with charge := (1312007311 / 1000000000000 : ℝ) }

theorem agent_is_repriced12039 : agent12039 =
    BstLean.Part265.agentRepriced 12039 world12039 paperAgent12039 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12039, agent12039]

noncomputable def paperAgent12040 : AgentParameters :=
  { agent12040 with charge := (327910913 / 250000000000 : ℝ) }

theorem agent_is_repriced12040 : agent12040 =
    BstLean.Part265.agentRepriced 12040 world12040 paperAgent12040 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12040, agent12040]

noncomputable def paperAgent12041 : AgentParameters :=
  { agent12041 with charge := (1311280453 / 1000000000000 : ℝ) }

theorem agent_is_repriced12041 : agent12041 =
    BstLean.Part265.agentRepriced 12041 world12041 paperAgent12041 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12041, agent12041]

noncomputable def paperAgent12042 : AgentParameters :=
  { agent12042 with charge := (655458857 / 500000000000 : ℝ) }

theorem agent_is_repriced12042 : agent12042 =
    BstLean.Part265.agentRepriced 12042 world12042 paperAgent12042 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12042, agent12042]

noncomputable def paperAgent12043 : AgentParameters :=
  { agent12043 with charge := (655277717 / 500000000000 : ℝ) }

theorem agent_is_repriced12043 : agent12043 =
    BstLean.Part265.agentRepriced 12043 world12043 paperAgent12043 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12043, agent12043]

noncomputable def paperAgent12044 : AgentParameters :=
  { agent12044 with charge := (327548403 / 250000000000 : ℝ) }

theorem agent_is_repriced12044 : agent12044 =
    BstLean.Part265.agentRepriced 12044 world12044 paperAgent12044 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12044, agent12044]

noncomputable def paperAgent12045 : AgentParameters :=
  { agent12045 with charge := (163729031 / 125000000000 : ℝ) }

theorem agent_is_repriced12045 : agent12045 =
    BstLean.Part265.agentRepriced 12045 world12045 paperAgent12045 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12045, agent12045]

noncomputable def paperAgent12046 : AgentParameters :=
  { agent12046 with charge := (1309471341 / 1000000000000 : ℝ) }

theorem agent_is_repriced12046 : agent12046 =
    BstLean.Part265.agentRepriced 12046 world12046 paperAgent12046 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12046, agent12046]

noncomputable def paperAgent12047 : AgentParameters :=
  { agent12047 with charge := (1309110891 / 1000000000000 : ℝ) }

theorem agent_is_repriced12047 : agent12047 =
    BstLean.Part265.agentRepriced 12047 world12047 paperAgent12047 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12047, agent12047]

noncomputable def paperAgent12048 : AgentParameters :=
  { agent12048 with charge := (261750179 / 200000000000 : ℝ) }

theorem agent_is_repriced12048 : agent12048 =
    BstLean.Part265.agentRepriced 12048 world12048 paperAgent12048 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12048, agent12048]

noncomputable def paperAgent12049 : AgentParameters :=
  { agent12049 with charge := (261678271 / 200000000000 : ℝ) }

theorem agent_is_repriced12049 : agent12049 =
    BstLean.Part265.agentRepriced 12049 world12049 paperAgent12049 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12049, agent12049]

noncomputable def paperAgent12050 : AgentParameters :=
  { agent12050 with charge := (1308032269 / 1000000000000 : ℝ) }

theorem agent_is_repriced12050 : agent12050 =
    BstLean.Part265.agentRepriced 12050 world12050 paperAgent12050 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12050, agent12050]

noncomputable def paperAgent12051 : AgentParameters :=
  { agent12051 with charge := (261534727 / 200000000000 : ℝ) }

theorem agent_is_repriced12051 : agent12051 =
    BstLean.Part265.agentRepriced 12051 world12051 paperAgent12051 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12051, agent12051]

noncomputable def paperAgent12052 : AgentParameters :=
  { agent12052 with charge := (5106701 / 3906250000 : ℝ) }

theorem agent_is_repriced12052 : agent12052 =
    BstLean.Part265.agentRepriced 12052 world12052 paperAgent12052 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12052, agent12052]

noncomputable def paperAgent12053 : AgentParameters :=
  { agent12053 with charge := (1306957729 / 1000000000000 : ℝ) }

theorem agent_is_repriced12053 : agent12053 =
    BstLean.Part265.agentRepriced 12053 world12053 paperAgent12053 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12053, agent12053]

noncomputable def paperAgent12054 : AgentParameters :=
  { agent12054 with charge := (326650113 / 250000000000 : ℝ) }

theorem agent_is_repriced12054 : agent12054 =
    BstLean.Part265.agentRepriced 12054 world12054 paperAgent12054 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12054, agent12054]

noncomputable def paperAgent12055 : AgentParameters :=
  { agent12055 with charge := (1306243627 / 1000000000000 : ℝ) }

theorem agent_is_repriced12055 : agent12055 =
    BstLean.Part265.agentRepriced 12055 world12055 paperAgent12055 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12055, agent12055]

noncomputable def paperAgent12056 : AgentParameters :=
  { agent12056 with charge := (1305887251 / 1000000000000 : ℝ) }

theorem agent_is_repriced12056 : agent12056 =
    BstLean.Part265.agentRepriced 12056 world12056 paperAgent12056 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12056, agent12056]

noncomputable def paperAgent12057 : AgentParameters :=
  { agent12057 with charge := (652765663 / 500000000000 : ℝ) }

theorem agent_is_repriced12057 : agent12057 =
    BstLean.Part265.agentRepriced 12057 world12057 paperAgent12057 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12057, agent12057]

noncomputable def paperAgent12058 : AgentParameters :=
  { agent12058 with charge := (163146981 / 125000000000 : ℝ) }

theorem agent_is_repriced12058 : agent12058 =
    BstLean.Part265.agentRepriced 12058 world12058 paperAgent12058 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12058, agent12058]

end BstLean.Part281
