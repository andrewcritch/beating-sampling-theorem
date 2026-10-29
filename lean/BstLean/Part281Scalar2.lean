import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 11909 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11909. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11909 : WorldParameters where
  hiddenCharge := (1210498349 / 1000000000000 : ℝ)
  frame := (637322022337 / 1000000000000 : ℝ)
  moment := (5574309523 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11909 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (294758222511 / 200000000000 : ℝ)
    root := (3634299793 / 500000000000 : ℝ) }

noncomputable def scalar11909 : ScalarCertificate 11909 world11909 agent11909 where
  dimensionLo := 11909
  dimensionHi := 11909
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2393164799 / 1000000000000 : ℝ)
  frameLo := (637322022337 / 1000000000000 : ℝ)
  frameHi := (294758222511 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11909]
  agentFrame_pos := by norm_num only [agent11909]
  worldRadius := (2393164799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11909]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (637007507 / 500000000000 : ℝ)
  lowerTail := (651311 / 400000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1964666219 / 250000000000 : ℝ)
  ledger := by
    have h : (1210498349 / 1000000000000 : ℚ) +
        (5574309523 / 500000000000000000 : ℚ) / (2393164799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (637007507 / 500000000000 : ℚ) + (651311 / 400000000 : ℚ) ≤
        (1964666219 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1210498349 / 1000000000000 : ℚ) +
        (5574309523 / 500000000000000000 : ℚ) / (2393164799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (637007507 / 500000000000 : ℚ) + (651311 / 400000000 : ℚ) : ℚ) : ℝ) ≤
        ((1964666219 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11909]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11909 :
    2 * 160 < 11909 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995577 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11909 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11910 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11910. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11910 : WorldParameters where
  hiddenCharge := (121044421 / 100000000000 : ℝ)
  frame := (637306227573 / 1000000000000 : ℝ)
  moment := (11146166041 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11910 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473745369701 / 1000000000000 : ℝ)
    root := (1816980483 / 250000000000 : ℝ) }

noncomputable def scalar11910 : ScalarCertificate 11910 world11910 agent11910 where
  dimensionLo := 11910
  dimensionHi := 11910
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2393578899 / 1000000000000 : ℝ)
  frameLo := (637306227573 / 1000000000000 : ℝ)
  frameHi := (1473745369701 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11910]
  agentFrame_pos := by norm_num only [agent11910]
  worldRadius := (2393578899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11910]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (3182163 / 2500000000 : ℝ)
  lowerTail := (1626917761 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7854999469 / 1000000000000 : ℝ)
  ledger := by
    have h : (121044421 / 100000000000 : ℚ) +
        (11146166041 / 1000000000000000000 : ℚ) / (2393578899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (3182163 / 2500000000 : ℚ) + (1626917761 / 1000000000000 : ℚ) ≤
        (7854999469 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((121044421 / 100000000000 : ℚ) +
        (11146166041 / 1000000000000000000 : ℚ) / (2393578899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (3182163 / 2500000000 : ℚ) + (1626917761 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7854999469 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11910]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11910 :
    2 * 160 < 11910 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998819 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11910 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11911 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11911. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11911 : WorldParameters where
  hiddenCharge := (1210390087 / 1000000000000 : ℝ)
  frame := (637290435549 / 1000000000000 : ℝ)
  moment := (1114371379 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11911 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368424912873 / 250000000000 : ℝ)
    root := (3633622259 / 500000000000 : ℝ) }

noncomputable def scalar11911 : ScalarCertificate 11911 world11911 agent11911 where
  dimensionLo := 11911
  dimensionHi := 11911
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2393992999 / 1000000000000 : ℝ)
  frameLo := (637290435549 / 1000000000000 : ℝ)
  frameHi := (368424912873 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11911]
  agentFrame_pos := by norm_num only [agent11911]
  worldRadius := (2393992999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11911]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (4967643 / 3906250000 : ℝ)
  lowerTail := (81277969 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1962834359 / 250000000000 : ℝ)
  ledger := by
    have h : (1210390087 / 1000000000000 : ℚ) +
        (1114371379 / 100000000000000000 : ℚ) / (2393992999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (4967643 / 3906250000 : ℚ) + (81277969 / 50000000000 : ℚ) ≤
        (1962834359 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1210390087 / 1000000000000 : ℚ) +
        (1114371379 / 100000000000000000 : ℚ) / (2393992999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (4967643 / 3906250000 : ℚ) + (81277969 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1962834359 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11911]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11911 :
    2 * 160 < 11911 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1099999901 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11911 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11912 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11912. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11912 : WorldParameters where
  hiddenCharge := (605167989 / 500000000000 : ℝ)
  frame := (127454929253 / 200000000000 : ℝ)
  moment := (11141262293 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11912 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473653957913 / 1000000000000 : ℝ)
    root := (7266567423 / 1000000000000 : ℝ) }

noncomputable def scalar11912 : ScalarCertificate 11912 world11912 agent11912 where
  dimensionLo := 11912
  dimensionHi := 11912
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2394406999 / 1000000000000 : ℝ)
  frameLo := (127454929253 / 200000000000 : ℝ)
  frameHi := (1473653957913 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11912]
  agentFrame_pos := by norm_num only [agent11912]
  worldRadius := (2394406999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11912]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (63528461 / 50000000000 : ℝ)
  lowerTail := (1624202333 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1569535779 / 200000000000 : ℝ)
  ledger := by
    have h : (605167989 / 500000000000 : ℚ) +
        (11141262293 / 1000000000000000000 : ℚ) / (2394406999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (63528461 / 50000000000 : ℚ) + (1624202333 / 1000000000000 : ℚ) ≤
        (1569535779 / 200000000000 : ℚ) := by norm_num only
    have hc : (((605167989 / 500000000000 : ℚ) +
        (11141262293 / 1000000000000000000 : ℚ) / (2394406999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (63528461 / 50000000000 : ℚ) + (1624202333 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1569535779 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11912]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11912 :
    2 * 160 < 11912 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999831 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11912 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11913 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11913. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11913 : WorldParameters where
  hiddenCharge := (242056377 / 200000000000 : ℝ)
  frame := (15931471493 / 25000000000 : ℝ)
  moment := (11138811549 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11913 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (29472165779 / 20000000000 : ℝ)
    root := (908236311 / 125000000000 : ℝ) }

noncomputable def scalar11913 : ScalarCertificate 11913 world11913 agent11913 where
  dimensionLo := 11913
  dimensionHi := 11913
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2394821199 / 1000000000000 : ℝ)
  frameLo := (15931471493 / 25000000000 : ℝ)
  frameHi := (29472165779 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11913]
  agentFrame_pos := by norm_num only [agent11913]
  worldRadius := (2394821199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11913]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1269423143 / 1000000000000 : ℝ)
  lowerTail := (811423377 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7844023597 / 1000000000000 : ℝ)
  ledger := by
    have h : (242056377 / 200000000000 : ℚ) +
        (11138811549 / 1000000000000000000 : ℚ) / (2394821199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1269423143 / 1000000000000 : ℚ) + (811423377 / 500000000000 : ℚ) ≤
        (7844023597 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((242056377 / 200000000000 : ℚ) +
        (11138811549 / 1000000000000000000 : ℚ) / (2394821199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1269423143 / 1000000000000 : ℚ) + (811423377 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7844023597 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11913]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11913 :
    2 * 160 < 11913 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999913 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11913 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11914 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11914. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11914 : WorldParameters where
  hiddenCharge := (1210227807 / 1000000000000 : ℝ)
  frame := (318621537957 / 500000000000 : ℝ)
  moment := (5568180779 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11914 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368390661147 / 250000000000 : ℝ)
    root := (7265213793 / 1000000000000 : ℝ) }

noncomputable def scalar11914 : ScalarCertificate 11914 world11914 agent11914 where
  dimensionLo := 11914
  dimensionHi := 11914
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2395235299 / 1000000000000 : ℝ)
  frameLo := (318621537957 / 500000000000 : ℝ)
  frameHi := (368390661147 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11914]
  agentFrame_pos := by norm_num only [agent11914]
  worldRadius := (2395235299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11914]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (19816847 / 15625000000 : ℝ)
  lowerTail := (1621492441 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (490023229 / 62500000000 : ℝ)
  ledger := by
    have h : (1210227807 / 1000000000000 : ℚ) +
        (5568180779 / 500000000000000000 : ℚ) / (2395235299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (19816847 / 15625000000 : ℚ) + (1621492441 / 1000000000000 : ℚ) ≤
        (490023229 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1210227807 / 1000000000000 : ℚ) +
        (5568180779 / 500000000000000000 : ℚ) / (2395235299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (19816847 / 15625000000 : ℚ) + (1621492441 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((490023229 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11914]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11914 :
    2 * 160 < 11914 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998689 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11914 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11915 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11915. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11915 : WorldParameters where
  hiddenCharge := (242034749 / 200000000000 : ℝ)
  frame := (127445458969 / 200000000000 : ℝ)
  moment := (8698369 / 781250000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11915 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473517024813 / 1000000000000 : ℝ)
    root := (908067177 / 125000000000 : ℝ) }

noncomputable def scalar11915 : ScalarCertificate 11915 world11915 agent11915 where
  dimensionLo := 11915
  dimensionHi := 11915
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2395649299 / 1000000000000 : ℝ)
  frameLo := (127445458969 / 200000000000 : ℝ)
  frameHi := (1473517024813 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11915]
  agentFrame_pos := by norm_num only [agent11915]
  worldRadius := (2395649299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11915]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (633567237 / 500000000000 : ℝ)
  lowerTail := (25314679 / 15625000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (783672321 / 100000000000 : ℝ)
  ledger := by
    have h : (242034749 / 200000000000 : ℚ) +
        (8698369 / 781250000000000 : ℚ) / (2395649299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (633567237 / 500000000000 : ℚ) + (25314679 / 15625000000 : ℚ) ≤
        (783672321 / 100000000000 : ℚ) := by norm_num only
    have hc : (((242034749 / 200000000000 : ℚ) +
        (8698369 / 781250000000000 : ℚ) / (2395649299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (633567237 / 500000000000 : ℚ) + (25314679 / 15625000000 : ℚ) : ℚ) : ℝ) ≤
        ((783672321 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11915]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11915 :
    2 * 160 < 11915 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997003 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11915 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11916 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11916. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11916 : WorldParameters where
  hiddenCharge := (1210119697 / 1000000000000 : ℝ)
  frame := (318605758257 / 500000000000 : ℝ)
  moment := (5565731917 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11916 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147347142961 / 100000000000 : ℝ)
    root := (7263861199 / 1000000000000 : ℝ) }

noncomputable def scalar11916 : ScalarCertificate 11916 world11916 agent11916 where
  dimensionLo := 11916
  dimensionHi := 11916
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2396063399 / 1000000000000 : ℝ)
  frameLo := (318605758257 / 500000000000 : ℝ)
  frameHi := (147347142961 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11916]
  agentFrame_pos := by norm_num only [agent11916]
  worldRadius := (2396063399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11916]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1265991971 / 1000000000000 : ℝ)
  lowerTail := (202348481 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (783307799 / 100000000000 : ℝ)
  ledger := by
    have h : (1210119697 / 1000000000000 : ℚ) +
        (5565731917 / 500000000000000000 : ℚ) / (2396063399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1265991971 / 1000000000000 : ℚ) + (202348481 / 125000000000 : ℚ) ≤
        (783307799 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1210119697 / 1000000000000 : ℚ) +
        (5565731917 / 500000000000000000 : ℚ) / (2396063399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1265991971 / 1000000000000 : ℚ) + (202348481 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((783307799 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11916]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11916 :
    2 * 160 < 11916 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994479 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11916 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11917 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11917. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11917 : WorldParameters where
  hiddenCharge := (242013133 / 200000000000 : ℝ)
  frame := (318597870459 / 500000000000 : ℝ)
  moment := (11129016101 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11917 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736712926501 / 500000000000 : ℝ)
    root := (363159261 / 50000000000 : ℝ) }

noncomputable def scalar11917 : ScalarCertificate 11917 world11917 agent11917 where
  dimensionLo := 11917
  dimensionHi := 11917
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2396477599 / 1000000000000 : ℝ)
  frameLo := (318597870459 / 500000000000 : ℝ)
  frameHi := (736712926501 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11917]
  agentFrame_pos := by norm_num only [agent11917]
  worldRadius := (2396477599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11917]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1264850731 / 1000000000000 : ℝ)
  lowerTail := (323487529 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7829436067 / 1000000000000 : ℝ)
  ledger := by
    have h : (242013133 / 200000000000 : ℚ) +
        (11129016101 / 1000000000000000000 : ℚ) / (2396477599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1264850731 / 1000000000000 : ℚ) + (323487529 / 200000000000 : ℚ) ≤
        (7829436067 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((242013133 / 200000000000 : ℚ) +
        (11129016101 / 1000000000000000000 : ℚ) / (2396477599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1264850731 / 1000000000000 : ℚ) + (323487529 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7829436067 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11917]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11917 :
    2 * 160 < 11917 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999623 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11917 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11918 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11918. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11918 : WorldParameters where
  hiddenCharge := (1210011649 / 1000000000000 : ℝ)
  frame := (637179968057 / 1000000000000 : ℝ)
  moment := (11126569119 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11918 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736690150469 / 500000000000 : ℝ)
    root := (181562737 / 25000000000 : ℝ) }

noncomputable def scalar11918 : ScalarCertificate 11918 world11918 agent11918 where
  dimensionLo := 11918
  dimensionHi := 11918
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2396891699 / 1000000000000 : ℝ)
  frameLo := (637179968057 / 1000000000000 : ℝ)
  frameHi := (736690150469 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11918]
  agentFrame_pos := by norm_num only [agent11918]
  worldRadius := (2396891699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11918]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1263710629 / 1000000000000 : ℝ)
  lowerTail := (1616088703 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1956449373 / 250000000000 : ℝ)
  ledger := by
    have h : (1210011649 / 1000000000000 : ℚ) +
        (11126569119 / 1000000000000000000 : ℚ) / (2396891699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1263710629 / 1000000000000 : ℚ) + (1616088703 / 1000000000000 : ℚ) ≤
        (1956449373 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1210011649 / 1000000000000 : ℚ) +
        (11126569119 / 1000000000000000000 : ℚ) / (2396891699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1263710629 / 1000000000000 : ℚ) + (1616088703 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1956449373 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11918]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11918 :
    2 * 160 < 11918 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999719 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11918 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11919 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11919. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11919 : WorldParameters where
  hiddenCharge := (1209957647 / 1000000000000 : ℝ)
  frame := (159291049483 / 250000000000 : ℝ)
  moment := (11124122889 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11919 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368333693351 / 250000000000 : ℝ)
    root := (7261834059 / 1000000000000 : ℝ) }

noncomputable def scalar11919 : ScalarCertificate 11919 world11919 agent11919 where
  dimensionLo := 11919
  dimensionHi := 11919
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2397305699 / 1000000000000 : ℝ)
  frameLo := (159291049483 / 250000000000 : ℝ)
  frameHi := (368333693351 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11919]
  agentFrame_pos := by norm_num only [agent11919]
  worldRadius := (2397305699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11919]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (631285861 / 500000000000 : ℝ)
  lowerTail := (1614741083 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7822162383 / 1000000000000 : ℝ)
  ledger := by
    have h : (1209957647 / 1000000000000 : ℚ) +
        (11124122889 / 1000000000000000000 : ℚ) / (2397305699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (631285861 / 500000000000 : ℚ) + (1614741083 / 1000000000000 : ℚ) ≤
        (7822162383 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1209957647 / 1000000000000 : ℚ) +
        (11124122889 / 1000000000000000000 : ℚ) / (2397305699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (631285861 / 500000000000 : ℚ) + (1614741083 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7822162383 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11919]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11919 :
    2 * 160 < 11919 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999283 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11919 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11920 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11920. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11920 : WorldParameters where
  hiddenCharge := (1209903661 / 1000000000000 : ℝ)
  frame := (31857421527 / 50000000000 : ℝ)
  moment := (1112167741 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11920 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736644635193 / 500000000000 : ℝ)
    root := (1815289699 / 250000000000 : ℝ) }

noncomputable def scalar11920 : ScalarCertificate 11920 world11920 agent11920 where
  dimensionLo := 11920
  dimensionHi := 11920
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2397719799 / 1000000000000 : ℝ)
  frameLo := (31857421527 / 50000000000 : ℝ)
  frameHi := (736644635193 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11920]
  agentFrame_pos := by norm_num only [agent11920]
  worldRadius := (2397719799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11920]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1261434039 / 1000000000000 : ℝ)
  lowerTail := (100837177 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (781853049 / 100000000000 : ℝ)
  ledger := by
    have h : (1209903661 / 1000000000000 : ℚ) +
        (1112167741 / 100000000000000000 : ℚ) / (2397719799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1261434039 / 1000000000000 : ℚ) + (100837177 / 62500000000 : ℚ) ≤
        (781853049 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1209903661 / 1000000000000 : ℚ) +
        (1112167741 / 100000000000000000 : ℚ) / (2397719799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1261434039 / 1000000000000 : ℚ) + (100837177 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((781853049 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11920]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11920 :
    2 * 160 < 11920 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999509 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11920 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11921 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11921. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11921 : WorldParameters where
  hiddenCharge := (120984969 / 100000000000 : ℝ)
  frame := (637132665881 / 1000000000000 : ℝ)
  moment := (5559616341 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11921 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147324379187 / 100000000000 : ℝ)
    root := (7260483771 / 1000000000000 : ℝ) }

noncomputable def scalar11921 : ScalarCertificate 11921 world11921 agent11921 where
  dimensionLo := 11921
  dimensionHi := 11921
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2398133999 / 1000000000000 : ℝ)
  frameLo := (637132665881 / 1000000000000 : ℝ)
  frameHi := (147324379187 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11921]
  agentFrame_pos := by norm_num only [agent11921]
  worldRadius := (2398133999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11921]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1260297637 / 1000000000000 : ℝ)
  lowerTail := (1612050011 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (488431371 / 62500000000 : ℝ)
  ledger := by
    have h : (120984969 / 100000000000 : ℚ) +
        (5559616341 / 500000000000000000 : ℚ) / (2398133999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1260297637 / 1000000000000 : ℚ) + (1612050011 / 1000000000000 : ℚ) ≤
        (488431371 / 62500000000 : ℚ) := by norm_num only
    have hc : (((120984969 / 100000000000 : ℚ) +
        (5559616341 / 500000000000000000 : ℚ) / (2398133999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1260297637 / 1000000000000 : ℚ) + (1612050011 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((488431371 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11921]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11921 :
    2 * 160 < 11921 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999443 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11921 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11922 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11922. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11922 : WorldParameters where
  hiddenCharge := (241959147 / 200000000000 : ℝ)
  frame := (318558451977 / 500000000000 : ℝ)
  moment := (347399647 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11922 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473198337841 / 1000000000000 : ℝ)
    root := (907476123 / 125000000000 : ℝ) }

noncomputable def scalar11922 : ScalarCertificate 11922 world11922 agent11922 where
  dimensionLo := 11922
  dimensionHi := 11922
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2398548099 / 1000000000000 : ℝ)
  frameLo := (318558451977 / 500000000000 : ℝ)
  frameHi := (1473198337841 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11922]
  agentFrame_pos := by norm_num only [agent11922]
  worldRadius := (2398548099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11922]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (4918603 / 3906250000 : ℝ)
  lowerTail := (805353223 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3905638357 / 500000000000 : ℝ)
  ledger := by
    have h : (241959147 / 200000000000 : ℚ) +
        (347399647 / 31250000000000000 : ℚ) / (2398548099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (4918603 / 3906250000 : ℚ) + (805353223 / 500000000000 : ℚ) ≤
        (3905638357 / 500000000000 : ℚ) := by norm_num only
    have hc : (((241959147 / 200000000000 : ℚ) +
        (347399647 / 31250000000000000 : ℚ) / (2398548099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (4918603 / 3906250000 : ℚ) + (805353223 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3905638357 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11922]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11922 :
    2 * 160 < 11922 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997757 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11922 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11923 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11923. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11923 : WorldParameters where
  hiddenCharge := (604870897 / 500000000000 : ℝ)
  frame := (637101144759 / 1000000000000 : ℝ)
  moment := (5557172739 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11923 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473152902323 / 1000000000000 : ℝ)
    root := (1451826887 / 200000000000 : ℝ) }

noncomputable def scalar11923 : ScalarCertificate 11923 world11923 agent11923 where
  dimensionLo := 11923
  dimensionHi := 11923
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2398962199 / 1000000000000 : ℝ)
  frameLo := (637101144759 / 1000000000000 : ℝ)
  frameHi := (1473152902323 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11923]
  agentFrame_pos := by norm_num only [agent11923]
  worldRadius := (2398962199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11923]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1258028279 / 1000000000000 : ℝ)
  lowerTail := (1609364189 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7807654767 / 1000000000000 : ℝ)
  ledger := by
    have h : (604870897 / 500000000000 : ℚ) +
        (5557172739 / 500000000000000000 : ℚ) / (2398962199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1258028279 / 1000000000000 : ℚ) + (1609364189 / 1000000000000 : ℚ) ≤
        (7807654767 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((604870897 / 500000000000 : ℚ) +
        (5557172739 / 500000000000000000 : ℚ) / (2398962199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1258028279 / 1000000000000 : ℚ) + (1609364189 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7807654767 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11923]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11923 :
    2 * 160 < 11923 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (17599997 / 1600000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11923 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11924 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11924. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11924 : WorldParameters where
  hiddenCharge := (1209687869 / 1000000000000 : ℝ)
  frame := (127417077659 / 200000000000 : ℝ)
  moment := (11111903001 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11924 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736553694957 / 500000000000 : ℝ)
    root := (1814615051 / 250000000000 : ℝ) }

noncomputable def scalar11924 : ScalarCertificate 11924 world11924 agent11924 where
  dimensionLo := 11924
  dimensionHi := 11924
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2399376399 / 1000000000000 : ℝ)
  frameLo := (127417077659 / 200000000000 : ℝ)
  frameHi := (736553694957 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11924]
  agentFrame_pos := by norm_num only [agent11924]
  worldRadius := (2399376399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11924]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (125689513 / 100000000000 : ℝ)
  lowerTail := (804011449 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7804035349 / 1000000000000 : ℝ)
  ledger := by
    have h : (1209687869 / 1000000000000 : ℚ) +
        (11111903001 / 1000000000000000000 : ℚ) / (2399376399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (125689513 / 100000000000 : ℚ) + (804011449 / 500000000000 : ℚ) ≤
        (7804035349 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1209687869 / 1000000000000 : ℚ) +
        (11111903001 / 1000000000000000000 : ℚ) / (2399376399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (125689513 / 100000000000 : ℚ) + (804011449 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7804035349 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11924]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11924 :
    2 * 160 < 11924 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (687499827 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11924 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11925 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11925. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11925 : WorldParameters where
  hiddenCharge := (1209633959 / 1000000000000 : ℝ)
  frame := (637069634561 / 1000000000000 : ℝ)
  moment := (5554730637 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11925 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473061651573 / 1000000000000 : ℝ)
    root := (725778613 / 100000000000 : ℝ) }

noncomputable def scalar11925 : ScalarCertificate 11925 world11925 agent11925 where
  dimensionLo := 11925
  dimensionHi := 11925
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2399791099 / 1000000000000 : ℝ)
  frameLo := (637069634561 / 1000000000000 : ℝ)
  frameHi := (1473061651573 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11925]
  agentFrame_pos := by norm_num only [agent11925]
  worldRadius := (2399791099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11925]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (627881259 / 500000000000 : ℝ)
  lowerTail := (200835253 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (243763027 / 31250000000 : ℝ)
  ledger := by
    have h : (1209633959 / 1000000000000 : ℚ) +
        (5554730637 / 500000000000000000 : ℚ) / (2399791099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (627881259 / 500000000000 : ℚ) + (200835253 / 125000000000 : ℚ) ≤
        (243763027 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1209633959 / 1000000000000 : ℚ) +
        (5554730637 / 500000000000000000 : ℚ) / (2399791099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (627881259 / 500000000000 : ℚ) + (200835253 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((243763027 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11925]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11925 :
    2 * 160 < 11925 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999437 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11925 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11926 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11926. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11926 : WorldParameters where
  hiddenCharge := (241916013 / 200000000000 : ℝ)
  frame := (159263470889 / 250000000000 : ℝ)
  moment := (1388377537 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11926 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (184126992957 / 125000000000 : ℝ)
    root := (3628556147 / 500000000000 : ℝ) }

noncomputable def scalar11926 : ScalarCertificate 11926 world11926 agent11926 where
  dimensionLo := 11926
  dimensionHi := 11926
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2400205599 / 1000000000000 : ℝ)
  frameLo := (159263470889 / 250000000000 : ℝ)
  frameHi := (184126992957 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11926]
  agentFrame_pos := by norm_num only [agent11926]
  worldRadius := (2400205599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11926]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1254630983 / 1000000000000 : ℝ)
  lowerTail := (200667793 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1949200439 / 250000000000 : ℝ)
  ledger := by
    have h : (241916013 / 200000000000 : ℚ) +
        (1388377537 / 125000000000000000 : ℚ) / (2400205599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1254630983 / 1000000000000 : ℚ) + (200667793 / 125000000000 : ℚ) ≤
        (1949200439 / 250000000000 : ℚ) := by norm_num only
    have hc : (((241916013 / 200000000000 : ℚ) +
        (1388377537 / 125000000000000000 : ℚ) / (2400205599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1254630983 / 1000000000000 : ℚ) + (200667793 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1949200439 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11926]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11926 :
    2 * 160 < 11926 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749998957 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11926 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11927 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11927. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11927 : WorldParameters where
  hiddenCharge := (241905237 / 200000000000 : ℝ)
  frame := (7962976691 / 12500000000 : ℝ)
  moment := (2776145017 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11927 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736485127113 / 500000000000 : ℝ)
    root := (1451287739 / 200000000000 : ℝ) }

noncomputable def scalar11927 : ScalarCertificate 11927 world11927 agent11927 where
  dimensionLo := 11927
  dimensionHi := 11927
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2400620299 / 1000000000000 : ℝ)
  frameLo := (7962976691 / 12500000000 : ℝ)
  frameHi := (736485127113 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11927]
  agentFrame_pos := by norm_num only [agent11927]
  worldRadius := (2400620299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11927]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1253500773 / 1000000000000 : ℝ)
  lowerTail := (100250259 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1558637983 / 200000000000 : ℝ)
  ledger := by
    have h : (241905237 / 200000000000 : ℚ) +
        (2776145017 / 250000000000000000 : ℚ) / (2400620299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1253500773 / 1000000000000 : ℚ) + (100250259 / 62500000000 : ℚ) ≤
        (1558637983 / 200000000000 : ℚ) := by norm_num only
    have hc : (((241905237 / 200000000000 : ℚ) +
        (2776145017 / 250000000000000000 : ℚ) / (2400620299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1253500773 / 1000000000000 : ℚ) + (100250259 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((1558637983 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11927]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11927 :
    2 * 160 < 11927 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999757 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11927 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11928 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11928. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11928 : WorldParameters where
  hiddenCharge := (1209472321 / 1000000000000 : ℝ)
  frame := (637022389731 / 1000000000000 : ℝ)
  moment := (2775535147 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11928 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147292459519 / 100000000000 : ℝ)
    root := (7255765333 / 1000000000000 : ℝ) }

noncomputable def scalar11928 : ScalarCertificate 11928 world11928 agent11928 where
  dimensionLo := 11928
  dimensionHi := 11928
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2401034899 / 1000000000000 : ℝ)
  frameLo := (637022389731 / 1000000000000 : ℝ)
  frameHi := (147292459519 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11928]
  agentFrame_pos := by norm_num only [agent11928]
  worldRadius := (2401034899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11928]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (125237171 / 100000000000 : ℝ)
  lowerTail := (1602667221 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (12171221 / 1562500000 : ℝ)
  ledger := by
    have h : (1209472321 / 1000000000000 : ℚ) +
        (2775535147 / 250000000000000000 : ℚ) / (2401034899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (125237171 / 100000000000 : ℚ) + (1602667221 / 1000000000000 : ℚ) ≤
        (12171221 / 1562500000 : ℚ) := by norm_num only
    have hc : (((1209472321 / 1000000000000 : ℚ) +
        (2775535147 / 250000000000000000 : ℚ) / (2401034899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (125237171 / 100000000000 : ℚ) + (1602667221 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((12171221 / 1562500000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11928]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11928 :
    2 * 160 < 11928 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994401 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11928 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11929 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11929. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11929 : WorldParameters where
  hiddenCharge := (151177309 / 125000000000 : ℝ)
  frame := (63700664691 / 100000000000 : ℝ)
  moment := (11099701857 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11929 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472878954613 / 1000000000000 : ℝ)
    root := (113360817 / 15625000000 : ℝ) }

noncomputable def scalar11929 : ScalarCertificate 11929 world11929 agent11929 where
  dimensionLo := 11929
  dimensionHi := 11929
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2401449599 / 1000000000000 : ℝ)
  frameLo := (63700664691 / 100000000000 : ℝ)
  frameHi := (1472878954613 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11929]
  agentFrame_pos := by norm_num only [agent11929]
  worldRadius := (2401449599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11929]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1251243953 / 1000000000000 : ℝ)
  lowerTail := (6405327 / 4000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7785976347 / 1000000000000 : ℝ)
  ledger := by
    have h : (151177309 / 125000000000 : ℚ) +
        (11099701857 / 1000000000000000000 : ℚ) / (2401449599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1251243953 / 1000000000000 : ℚ) + (6405327 / 4000000000 : ℚ) ≤
        (7785976347 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((151177309 / 125000000000 : ℚ) +
        (11099701857 / 1000000000000000000 : ℚ) / (2401449599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1251243953 / 1000000000000 : ℚ) + (6405327 / 4000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7785976347 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11929]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11929 :
    2 * 160 < 11929 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (439999861 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11929 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11930 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11930. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11930 : WorldParameters where
  hiddenCharge := (1209364639 / 1000000000000 : ℝ)
  frame := (127398181363 / 200000000000 : ℝ)
  moment := (88778111 / 8000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11930 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736416669221 / 500000000000 : ℝ)
    root := (7254419399 / 1000000000000 : ℝ) }

noncomputable def scalar11930 : ScalarCertificate 11930 world11930 agent11930 where
  dimensionLo := 11930
  dimensionHi := 11930
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2401864099 / 1000000000000 : ℝ)
  frameLo := (127398181363 / 200000000000 : ℝ)
  frameHi := (736416669221 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11930]
  agentFrame_pos := by norm_num only [agent11930]
  worldRadius := (2401864099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11930]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (625058593 / 500000000000 : ℝ)
  lowerTail := (799998687 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7782374439 / 1000000000000 : ℝ)
  ledger := by
    have h : (1209364639 / 1000000000000 : ℚ) +
        (88778111 / 8000000000000000 : ℚ) / (2401864099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (625058593 / 500000000000 : ℚ) + (799998687 / 500000000000 : ℚ) ≤
        (7782374439 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1209364639 / 1000000000000 : ℚ) +
        (88778111 / 8000000000000000 : ℚ) / (2401864099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (625058593 / 500000000000 : ℚ) + (799998687 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7782374439 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11930]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11930 :
    2 * 160 < 11930 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (219999971 / 20000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11930 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11931 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11931. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11931 : WorldParameters where
  hiddenCharge := (60465541 / 50000000000 : ℝ)
  frame := (127395033889 / 200000000000 : ℝ)
  moment := (138685333 / 12500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11931 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472787752623 / 1000000000000 : ℝ)
    root := (7253746747 / 1000000000000 : ℝ) }

noncomputable def scalar11931 : ScalarCertificate 11931 world11931 agent11931 where
  dimensionLo := 11931
  dimensionHi := 11931
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2402278699 / 1000000000000 : ℝ)
  frameLo := (127395033889 / 200000000000 : ℝ)
  frameHi := (1472787752623 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11931]
  agentFrame_pos := by norm_num only [agent11931]
  worldRadius := (2402278699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11931]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (124899171 / 100000000000 : ℝ)
  lowerTail := (799332223 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (777877589 / 100000000000 : ℝ)
  ledger := by
    have h : (60465541 / 50000000000 : ℚ) +
        (138685333 / 12500000000000000 : ℚ) / (2402278699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (124899171 / 100000000000 : ℚ) + (799332223 / 500000000000 : ℚ) ≤
        (777877589 / 100000000000 : ℚ) := by norm_num only
    have hc : (((60465541 / 50000000000 : ℚ) +
        (138685333 / 12500000000000000 : ℚ) / (2402278699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (124899171 / 100000000000 : ℚ) + (799332223 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((777877589 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11931]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11931 :
    2 * 160 < 11931 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994591 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11931 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11932 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11932. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11932 : WorldParameters where
  hiddenCharge := (1209257017 / 1000000000000 : ℝ)
  frame := (1592398587 / 2500000000 : ℝ)
  moment := (11092390153 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11932 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472742185221 / 1000000000000 : ℝ)
    root := (1813268583 / 250000000000 : ℝ) }

noncomputable def scalar11932 : ScalarCertificate 11932 world11932 agent11932 where
  dimensionLo := 11932
  dimensionHi := 11932
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2402693399 / 1000000000000 : ℝ)
  frameLo := (1592398587 / 2500000000 : ℝ)
  frameHi := (1472742185221 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11932]
  agentFrame_pos := by norm_num only [agent11932]
  worldRadius := (2402693399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11932]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1247867477 / 1000000000000 : ℝ)
  lowerTail := (1597332901 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1943795147 / 250000000000 : ℝ)
  ledger := by
    have h : (1209257017 / 1000000000000 : ℚ) +
        (11092390153 / 1000000000000000000 : ℚ) / (2402693399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1247867477 / 1000000000000 : ℚ) + (1597332901 / 1000000000000 : ℚ) ≤
        (1943795147 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1209257017 / 1000000000000 : ℚ) +
        (11092390153 / 1000000000000000000 : ℚ) / (2402693399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1247867477 / 1000000000000 : ℚ) + (1597332901 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1943795147 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11932]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11932 :
    2 * 160 < 11932 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998161 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11932 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11933 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11933. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11933 : WorldParameters where
  hiddenCharge := (1209203229 / 1000000000000 : ℝ)
  frame := (3980898143 / 6250000000 : ℝ)
  moment := (5544977207 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11933 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472696642183 / 1000000000000 : ℝ)
    root := (7252402153 / 1000000000000 : ℝ) }

noncomputable def scalar11933 : ScalarCertificate 11933 world11933 agent11933 where
  dimensionLo := 11933
  dimensionHi := 11933
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2403107899 / 1000000000000 : ℝ)
  frameLo := (3980898143 / 6250000000 : ℝ)
  frameHi := (1472696642183 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11933]
  agentFrame_pos := by norm_num only [agent11933]
  worldRadius := (2403107899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11933]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1246744289 / 1000000000000 : ℝ)
  lowerTail := (159600251 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7771588583 / 1000000000000 : ℝ)
  ledger := by
    have h : (1209203229 / 1000000000000 : ℚ) +
        (5544977207 / 500000000000000000 : ℚ) / (2403107899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1246744289 / 1000000000000 : ℚ) + (159600251 / 100000000000 : ℚ) ≤
        (7771588583 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1209203229 / 1000000000000 : ℚ) +
        (5544977207 / 500000000000000000 : ℚ) / (2403107899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1246744289 / 1000000000000 : ℚ) + (159600251 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7771588583 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11933]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11933 :
    2 * 160 < 11933 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997861 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11933 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding11909 :
    (605249174403805977121 / 500000000000000000000000 : ℝ) ≤ world11909.hiddenCharge ∧
    (318661011168274755948941 / 500000000000000000000000 : ℝ) ≤ world11909.frame ∧
    (5574309523 / 500000000000000000 : ℝ) ≤ world11909.moment ∧
    (1473791112554320117689277 / 1000000000000000000000000 : ℝ) ≤ agent11909.frame ∧
    (1453719917167458166219 / 200000000000000000000000 : ℝ) ≤ agent11909.root ∧
    scalar11909.worldRadius ≤ (2393164799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (256135825772559354629 / 200000000000000000000000 : ℝ) ≤ agent11909.charge ∧
    (637007506707951743273 / 500000000000000000000000 : ℝ) ≤ scalar11909.upperTail ∧
    (101767343725822074921 / 62500000000000000000000 : ℝ) ≤ scalar11909.lowerTail ∧
    scalar11909.totalBudget ≤ (7858664876607966857863 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11909, agent11909, scalar11909] <;> simp only [true_and]

theorem source_rounding11910 :
    (1210444209745941962209 / 1000000000000000000000000 : ℝ) ≤ world11910.hiddenCharge ∧
    (159326556893050703361437 / 250000000000000000000000 : ℝ) ≤ world11910.frame ∧
    (11146166041 / 1000000000000000000 : ℝ) ≤ world11910.moment ∧
    (73687268485044712957911 / 50000000000000000000000 : ℝ) ≤ agent11910.frame ∧
    (7267921931795469764263 / 1000000000000000000000000 : ℝ) ≤ agent11910.root ∧
    scalar11910.worldRadius ≤ (2393578899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (160049773358362028799 / 125000000000000000000000 : ℝ) ≤ agent11910.charge ∧
    (79554074945732809553 / 62500000000000000000000 : ℝ) ≤ scalar11910.upperTail ∧
    (1626917760106176172329 / 1000000000000000000000000 : ℝ) ≤ scalar11910.lowerTail ∧
    scalar11910.totalBudget ≤ (7854999469333719987057 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11910, agent11910, scalar11910] <;> simp only [true_and]

theorem source_rounding11911 :
    (151298760750461478779 / 125000000000000000000000 : ℝ) ≤ world11911.hiddenCharge ∧
    (637290435548498952035663 / 1000000000000000000000000 : ℝ) ≤ world11911.frame ∧
    (1114371379 / 100000000000000000 : ℝ) ≤ world11911.moment ∧
    (1473699651491901560456923 / 1000000000000000000000000 : ℝ) ≤ agent11911.frame ∧
    (1816811129403479450977 / 250000000000000000000000 : ℝ) ≤ agent11911.root ∧
    scalar11911.worldRadius ≤ (2393992999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (640058762541200985583 / 500000000000000000000000 : ℝ) ≤ agent11911.charge ∧
    (158964575885592316269 / 125000000000000000000000 : ℝ) ≤ scalar11911.upperTail ∧
    (1625559379695189147023 / 1000000000000000000000000 : ℝ) ≤ scalar11911.lowerTail ∧
    scalar11911.totalBudget ≤ (392566871826342384223 / 50000000000000000000000 : ℝ) := by
  norm_num only [world11911, agent11911, scalar11911] <;> simp only [true_and]

theorem source_rounding11912 :
    (48413439103007559377 / 40000000000000000000000 : ℝ) ≤ world11912.hiddenCharge ∧
    (318637323132340151572427 / 500000000000000000000000 : ℝ) ≤ world11912.frame ∧
    (11141262293 / 1000000000000000000 : ℝ) ≤ world11912.moment ∧
    (368413489478230847626869 / 250000000000000000000000 : ℝ) ≤ agent11912.frame ∧
    (7266567422859369923427 / 1000000000000000000000000 : ℝ) ≤ agent11912.root ∧
    scalar11912.worldRadius ≤ (2394406999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (639918571596497980949 / 500000000000000000000000 : ℝ) ≤ agent11912.charge ∧
    (317642304969376489301 / 250000000000000000000000 : ℝ) ≤ scalar11912.upperTail ∧
    (1624202332379389088509 / 1000000000000000000000000 : ℝ) ≤ scalar11912.lowerTail ∧
    scalar11912.totalBudget ≤ (3923839447893808020487 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11912, agent11912, scalar11912] <;> simp only [true_and]

theorem source_rounding11913 :
    (605140942227383270403 / 500000000000000000000000 : ℝ) ≤ world11913.hiddenCharge ∧
    (637258859719989437147453 / 1000000000000000000000000 : ℝ) ≤ world11913.frame ∧
    (11138811549 / 1000000000000000000 : ℝ) ≤ world11913.moment ∧
    (368402072237389746595569 / 250000000000000000000000 : ℝ) ≤ agent11913.frame ∧
    (7265890487882695501607 / 1000000000000000000000000 : ℝ) ≤ agent11913.root ∧
    scalar11913.worldRadius ≤ (2394821199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (255911408176552155539 / 200000000000000000000000 : ℝ) ≤ agent11913.charge ∧
    (126942314230002595567 / 100000000000000000000000 : ℝ) ≤ scalar11913.upperTail ∧
    (811423376531358456267 / 500000000000000000000000 : ℝ) ≤ scalar11913.lowerTail ∧
    scalar11913.totalBudget ≤ (7844023597488771676593 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11913, agent11913, scalar11913] <;> simp only [true_and]

theorem source_rounding11914 :
    (1210227806636755790161 / 1000000000000000000000000 : ℝ) ≤ world11914.hiddenCharge ∧
    (19913846122302163505441 / 31250000000000000000000 : ℝ) ≤ world11914.frame ∧
    (5568180779 / 500000000000000000 : ℝ) ≤ world11914.moment ∧
    (294712528917485085993527 / 200000000000000000000000 : ℝ) ≤ agent11914.frame ∧
    (7265213792268005610897 / 1000000000000000000000000 : ℝ) ≤ agent11914.root ∧
    scalar11914.worldRadius ≤ (2395235299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1279277217836179034709 / 1000000000000000000000000 : ℝ) ≤ agent11914.charge ∧
    (634139103932999035563 / 500000000000000000000000 : ℝ) ≤ scalar11914.upperTail ∧
    (202686555042757779503 / 125000000000000000000000 : ℝ) ≤ scalar11914.lowerTail ∧
    scalar11914.totalBudget ≤ (7840371664448941029129 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11914, agent11914, scalar11914] <;> simp only [true_and]

theorem source_rounding11915 :
    (605086872057746104709 / 500000000000000000000000 : ℝ) ≤ world11915.hiddenCharge ∧
    (318613647422481450938967 / 500000000000000000000000 : ℝ) ≤ world11915.frame ∧
    (8698369 / 781250000000000 : ℝ) ≤ world11915.moment ∧
    (1473517024812157624658699 / 1000000000000000000000000 : ℝ) ≤ agent11915.frame ∧
    (908067176941467447827 / 125000000000000000000000 : ℝ) ≤ agent11915.root ∧
    scalar11915.worldRadius ≤ (2395649299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (79937354608633301463 / 62500000000000000000000 : ℝ) ≤ agent11915.charge ∧
    (633567236879940038197 / 500000000000000000000000 : ℝ) ≤ scalar11915.upperTail ∧
    (324027891193130539717 / 200000000000000000000000 : ℝ) ≤ scalar11915.lowerTail ∧
    scalar11915.totalBudget ≤ (1567344642182643736127 / 200000000000000000000000 : ℝ) := by
  norm_num only [world11915, agent11915, scalar11915] <;> simp only [true_and]

theorem source_rounding11916 :
    (1210119696885316956071 / 1000000000000000000000000 : ℝ) ≤ world11916.hiddenCharge ∧
    (63721151651311383378637 / 100000000000000000000000 : ℝ) ≤ world11916.frame ∧
    (5565731917 / 500000000000000000 : ℝ) ≤ world11916.moment ∧
    (1473471429609408272085667 / 1000000000000000000000000 : ℝ) ≤ agent11916.frame ∧
    (3631930599063524354123 / 500000000000000000000000 : ℝ) ≤ agent11916.root ∧
    scalar11916.worldRadius ≤ (2396063399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (255743681654780628547 / 200000000000000000000000 : ℝ) ≤ agent11916.charge ∧
    (1265991970261295318621 / 1000000000000000000000000 : ℝ) ≤ scalar11916.upperTail ∧
    (809393923576986813681 / 500000000000000000000000 : ℝ) ≤ scalar11916.lowerTail ∧
    scalar11916.totalBudget ≤ (156661559819869562753 / 20000000000000000000000 : ℝ) := by
  norm_num only [world11916, agent11916, scalar11916] <;> simp only [true_and]

theorem source_rounding11917 :
    (1210065664940569364109 / 1000000000000000000000000 : ℝ) ≤ world11917.hiddenCharge ∧
    (637195740917365837152773 / 1000000000000000000000000 : ℝ) ≤ world11917.frame ∧
    (11129016101 / 1000000000000000000 : ℝ) ≤ world11917.moment ∧
    (294685170600234241019951 / 200000000000000000000000 : ℝ) ≤ agent11917.frame ∧
    (7263185219587729098319 / 1000000000000000000000000 : ℝ) ≤ agent11917.root ∧
    scalar11917.worldRadius ≤ (2396477599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1278439421129169335171 / 1000000000000000000000000 : ℝ) ≤ agent11917.charge ∧
    (316212682724239588319 / 250000000000000000000000 : ℝ) ≤ scalar11917.upperTail ∧
    (1617437644404283613721 / 1000000000000000000000000 : ℝ) ≤ scalar11917.lowerTail ∧
    scalar11917.totalBudget ≤ (3914718033570085024343 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11917, agent11917, scalar11917] <;> simp only [true_and]

theorem source_rounding11918 :
    (605005824137797222411 / 500000000000000000000000 : ℝ) ≤ world11918.hiddenCharge ∧
    (31858998402848144983611 / 50000000000000000000000 : ℝ) ≤ world11918.frame ∧
    (11126569119 / 1000000000000000000 : ℝ) ≤ world11918.moment ∧
    (7366901504686707815247 / 5000000000000000000000 : ℝ) ≤ agent11918.frame ∧
    (3631254739874305613481 / 500000000000000000000000 : ℝ) ≤ agent11918.root ∧
    scalar11918.worldRadius ≤ (2396891699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (639080355995004261343 / 500000000000000000000000 : ℝ) ≤ agent11918.charge ∧
    (631855314475355245503 / 500000000000000000000000 : ℝ) ≤ scalar11918.upperTail ∧
    (1616088702216899255307 / 1000000000000000000000000 : ℝ) ≤ scalar11918.lowerTail ∧
    scalar11918.totalBudget ≤ (3912898746175645618061 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11918, agent11918, scalar11918] <;> simp only [true_and]

theorem source_rounding11919 :
    (604978823442369192589 / 500000000000000000000000 : ℝ) ≤ world11919.hiddenCharge ∧
    (318582098965574665354203 / 500000000000000000000000 : ℝ) ≤ world11919.frame ∧
    (11124122889 / 1000000000000000000 : ℝ) ≤ world11919.moment ∧
    (294666954680724967155447 / 200000000000000000000000 : ℝ) ≤ agent11919.frame ∧
    (1452366811611822370247 / 200000000000000000000000 : ℝ) ≤ agent11919.root ∧
    scalar11919.worldRadius ≤ (2397305699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (638941140271447521789 / 500000000000000000000000 : ℝ) ≤ agent11919.charge ∧
    (1262571721383668543047 / 1000000000000000000000000 : ℝ) ≤ scalar11919.upperTail ∧
    (807370541057249006661 / 500000000000000000000000 : ℝ) ≤ scalar11919.lowerTail ∧
    scalar11919.totalBudget ≤ (7822162383170127592911 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11919, agent11919, scalar11919] <;> simp only [true_and]

theorem source_rounding11920 :
    (48396146430494001867 / 40000000000000000000000 : ℝ) ≤ world11920.hiddenCharge ∧
    (7964355381739620452419 / 12500000000000000000000 : ℝ) ≤ world11920.frame ∧
    (1112167741 / 100000000000000000 : ℝ) ≤ world11920.moment ∧
    (1473289270385744218861479 / 1000000000000000000000000 : ℝ) ≤ agent11920.frame ∧
    (1815289698777167699501 / 250000000000000000000000 : ℝ) ≤ agent11920.root ∧
    scalar11920.worldRadius ≤ (2397719799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1277604126474699890203 / 1000000000000000000000000 : ℝ) ≤ agent11920.charge ∧
    (630717019242451039907 / 500000000000000000000000 : ℝ) ≤ scalar11920.upperTail ∧
    (161339483130046441937 / 100000000000000000000000 : ℝ) ≤ scalar11920.lowerTail ∧
    scalar11920.totalBudget ≤ (3909265245482381869239 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11920, agent11920, scalar11920] <;> simp only [true_and]

theorem source_rounding11921 :
    (302462422475695614947 / 250000000000000000000000 : ℝ) ≤ world11921.hiddenCharge ∧
    (637132665880268889847643 / 1000000000000000000000000 : ℝ) ≤ world11921.frame ∧
    (5559616341 / 500000000000000000 : ℝ) ≤ world11921.moment ∧
    (368310947967360147624387 / 250000000000000000000000 : ℝ) ≤ agent11921.frame ∧
    (726048377036403588129 / 100000000000000000000000 : ℝ) ≤ agent11921.root ∧
    scalar11921.worldRadius ≤ (2398133999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (638663124736345073801 / 500000000000000000000000 : ℝ) ≤ agent11921.charge ∧
    (630148818465828472751 / 500000000000000000000000 : ℝ) ≤ scalar11921.upperTail ∧
    (806025005495388475721 / 500000000000000000000000 : ℝ) ≤ scalar11921.lowerTail ∧
    scalar11921.totalBudget ≤ (312596077454436350539 / 40000000000000000000000 : ℝ) := by
  norm_num only [world11921, agent11921, scalar11921] <;> simp only [true_and]

theorem source_rounding11922 :
    (604897867150193418649 / 500000000000000000000000 : ℝ) ≤ world11922.hiddenCharge ∧
    (637116903953692103513639 / 1000000000000000000000000 : ℝ) ≤ world11922.frame ∧
    (347399647 / 31250000000000000 : ℝ) ≤ world11922.moment ∧
    (294639667568094497682139 / 200000000000000000000000 : ℝ) ≤ agent11922.frame ∧
    (1451961796732154952161 / 200000000000000000000000 : ℝ) ≤ agent11922.root ∧
    scalar11922.worldRadius ≤ (2398548099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (638524324612264216499 / 500000000000000000000000 : ℝ) ≤ agent11922.charge ∧
    (12591623670682304383 / 10000000000000000000000 : ℝ) ≤ scalar11922.upperTail ∧
    (322141289039864441469 / 200000000000000000000000 : ℝ) ≤ scalar11922.lowerTail ∧
    scalar11922.totalBudget ≤ (781127671402635895889 / 100000000000000000000000 : ℝ) := by
  norm_num only [world11922, agent11922, scalar11922] <;> simp only [true_and]

theorem source_rounding11923 :
    (604870896974760775663 / 500000000000000000000000 : ℝ) ≤ world11923.hiddenCharge ∧
    (637101144758684776504907 / 1000000000000000000000000 : ℝ) ≤ world11923.frame ∧
    (5557172739 / 500000000000000000 : ℝ) ≤ world11923.moment ∧
    (368288225580632026160461 / 250000000000000000000000 : ℝ) ≤ agent11923.frame ∧
    (7259134434834638758043 / 1000000000000000000000000 : ℝ) ≤ agent11923.root ∧
    scalar11923.worldRadius ≤ (2398962199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (19949551959660505253 / 15625000000000000000000 : ℝ) ≤ agent11923.charge ∧
    (19656691847814088719 / 15625000000000000000000 : ℝ) ≤ scalar11923.upperTail ∧
    (1609364188787758739173 / 1000000000000000000000000 : ℝ) ≤ scalar11923.lowerTail ∧
    scalar11923.totalBudget ≤ (97595684598574951003 / 12500000000000000000000 : ℝ) := by
  norm_num only [world11923, agent11923, scalar11923] <;> simp only [true_and]

theorem source_rounding11924 :
    (1209687868844547639073 / 1000000000000000000000000 : ℝ) ≤ world11924.hiddenCharge ∧
    (637085388294492602772547 / 1000000000000000000000000 : ℝ) ≤ world11924.frame ∧
    (11111903001 / 1000000000000000000 : ℝ) ≤ world11924.moment ∧
    (368276847478255523511713 / 250000000000000000000000 : ℝ) ≤ agent11924.frame ∧
    (7258460203251362903049 / 1000000000000000000000000 : ℝ) ≤ agent11924.root ∧
    scalar11924.worldRadius ≤ (2399376399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (39890446179449183151 / 31250000000000000000000 : ℝ) ≤ agent11924.charge ∧
    (628447564515279136829 / 500000000000000000000000 : ℝ) ≤ scalar11924.upperTail ∧
    (1608022897262486978887 / 1000000000000000000000000 : ℝ) ≤ scalar11924.lowerTail ∧
    scalar11924.totalBudget ≤ (7804035349057979348739 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11924, agent11924, scalar11924] <;> simp only [true_and]

theorem source_rounding11925 :
    (1209633958979824321761 / 1000000000000000000000000 : ℝ) ≤ world11925.hiddenCharge ∧
    (127413926912072325894089 / 200000000000000000000000 : ℝ) ≤ world11925.frame ∧
    (5554730637 / 500000000000000000 : ℝ) ≤ world11925.moment ∧
    (92066353223272846549319 / 62500000000000000000000 : ℝ) ≤ agent11925.frame ∧
    (3628893064835268734441 / 500000000000000000000000 : ℝ) ≤ agent11925.root ∧
    scalar11925.worldRadius ≤ (2399791099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1276217505885678866571 / 1000000000000000000000000 : ℝ) ≤ agent11925.charge ∧
    (627881258617104289321 / 500000000000000000000000 : ℝ) ≤ scalar11925.upperTail ∧
    (1606682023275358964199 / 1000000000000000000000000 : ℝ) ≤ scalar11925.lowerTail ∧
    scalar11925.totalBudget ≤ (121881513510367048231 / 15625000000000000000000 : ℝ) := by
  norm_num only [world11925, agent11925, scalar11925] <;> simp only [true_and]

theorem source_rounding11926 :
    (604790032174858238031 / 500000000000000000000000 : ℝ) ≤ world11926.hiddenCharge ∧
    (318526941777769074426283 / 500000000000000000000000 : ℝ) ≤ world11926.frame ∧
    (1388377537 / 125000000000000000 : ℝ) ≤ world11926.moment ∧
    (294603188731077121551673 / 200000000000000000000000 : ℝ) ≤ agent11926.frame ∧
    (1814278073368799115429 / 250000000000000000000000 : ℝ) ≤ agent11926.root ∧
    scalar11926.worldRadius ≤ (2400205599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1275941009537426512103 / 1000000000000000000000000 : ℝ) ≤ agent11926.charge ∧
    (1254630982477213749321 / 1000000000000000000000000 : ℝ) ≤ scalar11926.upperTail ∧
    (401335585926371266937 / 250000000000000000000000 : ℝ) ≤ scalar11926.lowerTail ∧
    scalar11926.totalBudget ≤ (3898400878314045540623 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11926, agent11926, scalar11926] <;> simp only [true_and]

theorem source_rounding11927 :
    (1209526184948593133463 / 1000000000000000000000000 : ℝ) ≤ world11927.hiddenCharge ∧
    (637038135279268799024251 / 1000000000000000000000000 : ℝ) ≤ world11927.frame ∧
    (2776145017 / 250000000000000000 : ℝ) ≤ world11927.moment ∧
    (294594050845011201910213 / 200000000000000000000000 : ℝ) ≤ agent11927.frame ∧
    (7256438694501823317513 / 1000000000000000000000000 : ℝ) ≤ agent11927.root ∧
    scalar11927.worldRadius ≤ (2400620299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1275664788387248699073 / 1000000000000000000000000 : ℝ) ≤ agent11927.charge ∧
    (1253500772035102312387 / 1000000000000000000000000 : ℝ) ≤ scalar11927.upperTail ∧
    (1604004143088143925147 / 1000000000000000000000000 : ℝ) ≤ scalar11927.lowerTail ∧
    scalar11927.totalBudget ≤ (1948297478814648457827 / 250000000000000000000000 : ℝ) := by
  norm_num only [world11927, agent11927, scalar11927] <;> simp only [true_and]

theorem source_rounding11928 :
    (302368080192705377797 / 250000000000000000000000 : ℝ) ≤ world11928.hiddenCharge ∧
    (637022389730800418847353 / 1000000000000000000000000 : ℝ) ≤ world11928.frame ∧
    (2775535147 / 250000000000000000 : ℝ) ≤ world11928.moment ∧
    (1472924595189524636485153 / 1000000000000000000000000 : ℝ) ≤ agent11928.frame ∧
    (145115306651741677421 / 20000000000000000000000 : ℝ) ≤ agent11928.root ∧
    scalar11928.worldRadius ≤ (2401034899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (637694421062584758437 / 500000000000000000000000 : ℝ) ≤ agent11928.charge ∧
    (1252371709525642581703 / 1000000000000000000000000 : ℝ) ≤ scalar11928.upperTail ∧
    (16026672207173927577 / 10000000000000000000000 : ℝ) ≤ scalar11928.lowerTail ∧
    scalar11928.totalBudget ≤ (7789581440789306648413 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11928, agent11928, scalar11928] <;> simp only [true_and]

theorem source_rounding11929 :
    (241883694362155192573 / 200000000000000000000000 : ℝ) ≤ world11929.hiddenCharge ∧
    (159251661727345009898767 / 250000000000000000000000 : ℝ) ≤ world11929.frame ∧
    (11099701857 / 1000000000000000000 : ℝ) ≤ world11929.moment ∧
    (736439477306433436403707 / 500000000000000000000000 : ℝ) ≤ agent11929.frame ∧
    (1451018457402634480897 / 200000000000000000000000 : ℝ) ≤ agent11929.root ∧
    scalar11929.worldRadius ≤ (2401449599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1275113170441604688309 / 1000000000000000000000000 : ℝ) ≤ agent11929.charge ∧
    (1251243952184214184929 / 1000000000000000000000000 : ℝ) ≤ scalar11929.upperTail ∧
    (1601331749506719242273 / 1000000000000000000000000 : ℝ) ≤ scalar11929.lowerTail ∧
    scalar11929.totalBudget ≤ (12457562155406962199 / 1600000000000000000000 : ℝ) := by
  norm_num only [world11929, agent11929, scalar11929] <;> simp only [true_and]

theorem source_rounding11930 :
    (151170579757853814811 / 125000000000000000000000 : ℝ) ≤ world11930.hiddenCharge ∧
    (79623863351781912172783 / 125000000000000000000000 : ℝ) ≤ world11930.frame ∧
    (88778111 / 8000000000000000 : ℝ) ≤ world11930.moment ∧
    (471306668301432395797 / 320000000000000000000 : ℝ) ≤ agent11930.frame ∧
    (7254419398709528643209 / 1000000000000000000000000 : ℝ) ≤ agent11930.root ∧
    scalar11930.worldRadius ≤ (2401864099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (19919340203552515877 / 15625000000000000000000 : ℝ) ≤ agent11930.charge ∧
    (31252929636695931107 / 25000000000000000000000 : ℝ) ≤ scalar11930.upperTail ∧
    (99999835864742250379 / 62500000000000000000000 : ℝ) ≤ scalar11930.lowerTail ∧
    scalar11930.totalBudget ≤ (3891187219860786400189 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11930, agent11930, scalar11930] <;> simp only [true_and]

theorem source_rounding11931 :
    (9674486556170894941 / 8000000000000000000000 : ℝ) ≤ world11931.hiddenCharge ∧
    (63697516944467377163053 / 100000000000000000000000 : ℝ) ≤ world11931.frame ∧
    (138685333 / 12500000000000000 : ℝ) ≤ world11931.moment ∧
    (736393876311349309149031 / 500000000000000000000000 : ℝ) ≤ agent11931.frame ∧
    (3626873373487806927927 / 500000000000000000000000 : ℝ) ≤ agent11931.root ∧
    scalar11931.worldRadius ≤ (2402278699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1274562649573635830453 / 1000000000000000000000000 : ℝ) ≤ agent11931.charge ∧
    (624495854790409666823 / 500000000000000000000000 : ℝ) ≤ scalar11931.upperTail ∧
    (1598664445240188931561 / 1000000000000000000000000 : ℝ) ≤ scalar11931.lowerTail ∧
    scalar11931.totalBudget ≤ (7778775890076499349091 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11931, agent11931, scalar11931] <;> simp only [true_and]

theorem source_rounding11932 :
    (604628508090375422913 / 500000000000000000000000 : ℝ) ≤ world11932.hiddenCharge ∧
    (159239858699970882645983 / 250000000000000000000000 : ℝ) ≤ world11932.frame ∧
    (11092390153 / 1000000000000000000 : ℝ) ≤ world11932.moment ∧
    (1472742185220759434594407 / 1000000000000000000000000 : ℝ) ≤ agent11932.frame ∧
    (3626537165824410479501 / 500000000000000000000000 : ℝ) ≤ agent11932.root ∧
    scalar11932.worldRadius ≤ (2402693399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (159285974971502054631 / 125000000000000000000000 : ℝ) ≤ agent11932.charge ∧
    (1247867476629484484173 / 1000000000000000000000000 : ℝ) ≤ scalar11932.upperTail ∧
    (798666450348288682557 / 500000000000000000000000 : ℝ) ≤ scalar11932.lowerTail ∧
    scalar11932.totalBudget ≤ (3887590294007650398859 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11932, agent11932, scalar11932] <;> simp only [true_and]

theorem source_rounding11933 :
    (1209203228035380942059 / 1000000000000000000000000 : ℝ) ≤ world11933.hiddenCharge ∧
    (63694370287913282679649 / 100000000000000000000000 : ℝ) ≤ world11933.frame ∧
    (5544977207 / 500000000000000000 : ℝ) ≤ world11933.moment ∧
    (368174160545576375195369 / 250000000000000000000000 : ℝ) ≤ agent11933.frame ∧
    (7252402152566724014663 / 1000000000000000000000000 : ℝ) ≤ agent11933.root ∧
    scalar11933.worldRadius ≤ (2403107899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (15925165291430994581 / 12500000000000000000000 : ℝ) ≤ agent11933.charge ∧
    (1246744288007591183033 / 1000000000000000000000000 : ℝ) ≤ scalar11933.upperTail ∧
    (1596002509799183039513 / 1000000000000000000000000 : ℝ) ≤ scalar11933.lowerTail ∧
    scalar11933.totalBudget ≤ (1942897145777997057813 / 250000000000000000000000 : ℝ) := by
  norm_num only [world11933, agent11933, scalar11933] <;> simp only [true_and]

noncomputable def paperAgent11909 : AgentParameters :=
  { agent11909 with charge := (320169783 / 250000000000 : ℝ) }

theorem agent_is_repriced11909 : agent11909 =
    BstLean.Part265.agentRepriced 11909 world11909 paperAgent11909 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11909, agent11909]

noncomputable def paperAgent11910 : AgentParameters :=
  { agent11910 with charge := (128039819 / 100000000000 : ℝ) }

theorem agent_is_repriced11910 : agent11910 =
    BstLean.Part265.agentRepriced 11910 world11910 paperAgent11910 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11910, agent11910]

noncomputable def paperAgent11911 : AgentParameters :=
  { agent11911 with charge := (160014691 / 125000000000 : ℝ) }

theorem agent_is_repriced11911 : agent11911 =
    BstLean.Part265.agentRepriced 11911 world11911 paperAgent11911 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11911, agent11911]

noncomputable def paperAgent11912 : AgentParameters :=
  { agent11912 with charge := (639918573 / 500000000000 : ℝ) }

theorem agent_is_repriced11912 : agent11912 =
    BstLean.Part265.agentRepriced 11912 world11912 paperAgent11912 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11912, agent11912]

noncomputable def paperAgent11913 : AgentParameters :=
  { agent11913 with charge := (255911409 / 200000000000 : ℝ) }

theorem agent_is_repriced11913 : agent11913 =
    BstLean.Part265.agentRepriced 11913 world11913 paperAgent11913 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11913, agent11913]

noncomputable def paperAgent11914 : AgentParameters :=
  { agent11914 with charge := (1279277221 / 1000000000000 : ℝ) }

theorem agent_is_repriced11914 : agent11914 =
    BstLean.Part265.agentRepriced 11914 world11914 paperAgent11914 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11914, agent11914]

noncomputable def paperAgent11915 : AgentParameters :=
  { agent11915 with charge := (1278997677 / 1000000000000 : ℝ) }

theorem agent_is_repriced11915 : agent11915 =
    BstLean.Part265.agentRepriced 11915 world11915 paperAgent11915 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11915, agent11915]

noncomputable def paperAgent11916 : AgentParameters :=
  { agent11916 with charge := (1278718411 / 1000000000000 : ℝ) }

theorem agent_is_repriced11916 : agent11916 =
    BstLean.Part265.agentRepriced 11916 world11916 paperAgent11916 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11916, agent11916]

noncomputable def paperAgent11917 : AgentParameters :=
  { agent11917 with charge := (51137577 / 40000000000 : ℝ) }

theorem agent_is_repriced11917 : agent11917 =
    BstLean.Part265.agentRepriced 11917 world11917 paperAgent11917 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11917, agent11917]

noncomputable def paperAgent11918 : AgentParameters :=
  { agent11918 with charge := (255632143 / 200000000000 : ℝ) }

theorem agent_is_repriced11918 : agent11918 =
    BstLean.Part265.agentRepriced 11918 world11918 paperAgent11918 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11918, agent11918]

noncomputable def paperAgent11919 : AgentParameters :=
  { agent11919 with charge := (1277882283 / 1000000000000 : ℝ) }

theorem agent_is_repriced11919 : agent11919 =
    BstLean.Part265.agentRepriced 11919 world11919 paperAgent11919 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11919, agent11919]

noncomputable def paperAgent11920 : AgentParameters :=
  { agent11920 with charge := (127760413 / 100000000000 : ℝ) }

theorem agent_is_repriced11920 : agent11920 =
    BstLean.Part265.agentRepriced 11920 world11920 paperAgent11920 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11920, agent11920]

noncomputable def paperAgent11921 : AgentParameters :=
  { agent11921 with charge := (1277326253 / 1000000000000 : ℝ) }

theorem agent_is_repriced11921 : agent11921 =
    BstLean.Part265.agentRepriced 11921 world11921 paperAgent11921 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11921, agent11921]

noncomputable def paperAgent11922 : AgentParameters :=
  { agent11922 with charge := (1277048653 / 1000000000000 : ℝ) }

theorem agent_is_repriced11922 : agent11922 =
    BstLean.Part265.agentRepriced 11922 world11922 paperAgent11922 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11922, agent11922]

noncomputable def paperAgent11923 : AgentParameters :=
  { agent11923 with charge := (1276771329 / 1000000000000 : ℝ) }

theorem agent_is_repriced11923 : agent11923 =
    BstLean.Part265.agentRepriced 11923 world11923 paperAgent11923 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11923, agent11923]

noncomputable def paperAgent11924 : AgentParameters :=
  { agent11924 with charge := (1276494281 / 1000000000000 : ℝ) }

theorem agent_is_repriced11924 : agent11924 =
    BstLean.Part265.agentRepriced 11924 world11924 paperAgent11924 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11924, agent11924]

noncomputable def paperAgent11925 : AgentParameters :=
  { agent11925 with charge := (1276217509 / 1000000000000 : ℝ) }

theorem agent_is_repriced11925 : agent11925 =
    BstLean.Part265.agentRepriced 11925 world11925 paperAgent11925 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11925, agent11925]

noncomputable def paperAgent11926 : AgentParameters :=
  { agent11926 with charge := (1275941013 / 1000000000000 : ℝ) }

theorem agent_is_repriced11926 : agent11926 =
    BstLean.Part265.agentRepriced 11926 world11926 paperAgent11926 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11926, agent11926]

noncomputable def paperAgent11927 : AgentParameters :=
  { agent11927 with charge := (1275664791 / 1000000000000 : ℝ) }

theorem agent_is_repriced11927 : agent11927 =
    BstLean.Part265.agentRepriced 11927 world11927 paperAgent11927 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11927, agent11927]

noncomputable def paperAgent11928 : AgentParameters :=
  { agent11928 with charge := (637694423 / 500000000000 : ℝ) }

theorem agent_is_repriced11928 : agent11928 =
    BstLean.Part265.agentRepriced 11928 world11928 paperAgent11928 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11928, agent11928]

noncomputable def paperAgent11929 : AgentParameters :=
  { agent11929 with charge := (1275113173 / 1000000000000 : ℝ) }

theorem agent_is_repriced11929 : agent11929 =
    BstLean.Part265.agentRepriced 11929 world11929 paperAgent11929 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11929, agent11929]

noncomputable def paperAgent11930 : AgentParameters :=
  { agent11930 with charge := (79677361 / 62500000000 : ℝ) }

theorem agent_is_repriced11930 : agent11930 =
    BstLean.Part265.agentRepriced 11930 world11930 paperAgent11930 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11930, agent11930]

noncomputable def paperAgent11931 : AgentParameters :=
  { agent11931 with charge := (1274562653 / 1000000000000 : ℝ) }

theorem agent_is_repriced11931 : agent11931 =
    BstLean.Part265.agentRepriced 11931 world11931 paperAgent11931 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11931, agent11931]

noncomputable def paperAgent11932 : AgentParameters :=
  { agent11932 with charge := (1274287803 / 1000000000000 : ℝ) }

theorem agent_is_repriced11932 : agent11932 =
    BstLean.Part265.agentRepriced 11932 world11932 paperAgent11932 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11932, agent11932]

noncomputable def paperAgent11933 : AgentParameters :=
  { agent11933 with charge := (1274013227 / 1000000000000 : ℝ) }

theorem agent_is_repriced11933 : agent11933 =
    BstLean.Part265.agentRepriced 11933 world11933 paperAgent11933 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11933, agent11933]

end BstLean.Part281
