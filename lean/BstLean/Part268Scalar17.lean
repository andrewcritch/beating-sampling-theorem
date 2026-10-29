import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12775 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12775. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12775 : WorldParameters where
  hiddenCharge := (1168795109 / 1000000000000 : ℝ)
  frame := (624594669261 / 1000000000000 : ℝ)
  moment := (2322082893 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12775 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (46035264689 / 31250000000 : ℝ)
    root := (8444904289 / 1000000000000 : ℝ) }

noncomputable def scalar12775 : ScalarCertificate 12775 world12775 agent12775 where
  dimensionLo := 12775
  dimensionHi := 12775
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2204809899 / 1000000000000 : ℝ)
  frameLo := (624594669261 / 1000000000000 : ℝ)
  frameHi := (46035264689 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12775]
  agentFrame_pos := by norm_num only [agent12775]
  worldRadius := (2204809899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12775]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (341635323 / 250000000000 : ℝ)
  lowerTail := (1622061099 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7867256281 / 1000000000000 : ℝ)
  ledger := by
    have h : (1168795109 / 1000000000000 : ℚ) +
        (2322082893 / 250000000000000000 : ℚ) / (2204809899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (341635323 / 250000000000 : ℚ) + (1622061099 / 1000000000000 : ℚ) ≤
        (7867256281 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1168795109 / 1000000000000 : ℚ) +
        (2322082893 / 250000000000000000 : ℚ) / (2204809899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (341635323 / 250000000000 : ℚ) + (1622061099 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7867256281 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12775]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12775 :
    2 * 160 < 12775 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999579 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12775 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12776 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12776. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12776 : WorldParameters where
  hiddenCharge := (584376181 / 500000000000 : ℝ)
  frame := (624580992067 / 1000000000000 : ℝ)
  moment := (9286432081 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12776 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473097234181 / 1000000000000 : ℝ)
    root := (8444237451 / 1000000000000 : ℝ) }

noncomputable def scalar12776 : ScalarCertificate 12776 world12776 agent12776 where
  dimensionLo := 12776
  dimensionHi := 12776
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2205168199 / 1000000000000 : ℝ)
  frameLo := (624580992067 / 1000000000000 : ℝ)
  frameHi := (1473097234181 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12776]
  agentFrame_pos := by norm_num only [agent12776]
  worldRadius := (2205168199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12776]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1365394889 / 1000000000000 : ℝ)
  lowerTail := (810398799 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1965948037 / 250000000000 : ℝ)
  ledger := by
    have h : (584376181 / 500000000000 : ℚ) +
        (9286432081 / 1000000000000000000 : ℚ) / (2205168199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1365394889 / 1000000000000 : ℚ) + (810398799 / 500000000000 : ℚ) ≤
        (1965948037 / 250000000000 : ℚ) := by norm_num only
    have hc : (((584376181 / 500000000000 : ℚ) +
        (9286432081 / 1000000000000000000 : ℚ) / (2205168199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1365394889 / 1000000000000 : ℚ) + (810398799 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1965948037 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12776]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12776 :
    2 * 160 < 12776 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999721 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12776 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12777 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12777. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12777 : WorldParameters where
  hiddenCharge := (1168709627 / 1000000000000 : ℝ)
  frame := (624567317051 / 1000000000000 : ℝ)
  moment := (9284533133 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12777 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473066017791 / 1000000000000 : ℝ)
    root := (8443570749 / 1000000000000 : ℝ) }

noncomputable def scalar12777 : ScalarCertificate 12777 world12777 agent12777 where
  dimensionLo := 12777
  dimensionHi := 12777
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2205526399 / 1000000000000 : ℝ)
  frameLo := (624567317051 / 1000000000000 : ℝ)
  frameHi := (1473066017791 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12777]
  agentFrame_pos := by norm_num only [agent12777]
  worldRadius := (2205526399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12777]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1364249477 / 1000000000000 : ℝ)
  lowerTail := (12956281 / 8000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7860330887 / 1000000000000 : ℝ)
  ledger := by
    have h : (1168709627 / 1000000000000 : ℚ) +
        (9284533133 / 1000000000000000000 : ℚ) / (2205526399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1364249477 / 1000000000000 : ℚ) + (12956281 / 8000000000 : ℚ) ≤
        (7860330887 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1168709627 / 1000000000000 : ℚ) +
        (9284533133 / 1000000000000000000 : ℚ) / (2205526399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1364249477 / 1000000000000 : ℚ) + (12956281 / 8000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7860330887 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12777]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12777 :
    2 * 160 < 12777 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994733 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12777 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12778 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12778. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12778 : WorldParameters where
  hiddenCharge := (1168666903 / 1000000000000 : ℝ)
  frame := (624553644213 / 1000000000000 : ℝ)
  moment := (9282634727 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12778 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473034814971 / 1000000000000 : ℝ)
    root := (1688580863 / 200000000000 : ℝ) }

noncomputable def scalar12778 : ScalarCertificate 12778 world12778 agent12778 where
  dimensionLo := 12778
  dimensionHi := 12778
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2205884699 / 1000000000000 : ℝ)
  frameLo := (624553644213 / 1000000000000 : ℝ)
  frameHi := (1473034814971 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12778]
  agentFrame_pos := by norm_num only [agent12778]
  worldRadius := (2205884699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12778]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (681552651 / 500000000000 : ℝ)
  lowerTail := (1618273939 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (491054541 / 62500000000 : ℝ)
  ledger := by
    have h : (1168666903 / 1000000000000 : ℚ) +
        (9282634727 / 1000000000000000000 : ℚ) / (2205884699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (681552651 / 500000000000 : ℚ) + (1618273939 / 1000000000000 : ℚ) ≤
        (491054541 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1168666903 / 1000000000000 : ℚ) +
        (9282634727 / 1000000000000000000 : ℚ) / (2205884699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (681552651 / 500000000000 : ℚ) + (1618273939 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((491054541 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12778]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12778 :
    2 * 160 < 12778 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995373 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12778 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12779 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12779. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12779 : WorldParameters where
  hiddenCharge := (116862419 / 100000000000 : ℝ)
  frame := (624539973553 / 1000000000000 : ℝ)
  moment := (9280736863 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12779 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1473003625713 / 1000000000000 : ℝ)
    root := (8442238017 / 1000000000000 : ℝ) }

noncomputable def scalar12779 : ScalarCertificate 12779 world12779 agent12779 where
  dimensionLo := 12779
  dimensionHi := 12779
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2206242999 / 1000000000000 : ℝ)
  frameLo := (624539973553 / 1000000000000 : ℝ)
  frameHi := (1473003625713 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12779]
  agentFrame_pos := by norm_num only [agent12779]
  worldRadius := (2206242999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12779]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1361962173 / 1000000000000 : ℝ)
  lowerTail := (808506919 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1570683447 / 200000000000 : ℝ)
  ledger := by
    have h : (116862419 / 100000000000 : ℚ) +
        (9280736863 / 1000000000000000000 : ℚ) / (2206242999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1361962173 / 1000000000000 : ℚ) + (808506919 / 500000000000 : ℚ) ≤
        (1570683447 / 200000000000 : ℚ) := by norm_num only
    have hc : (((116862419 / 100000000000 : ℚ) +
        (9280736863 / 1000000000000000000 : ℚ) / (2206242999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1361962173 / 1000000000000 : ℚ) + (808506919 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1570683447 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12779]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12779 :
    2 * 160 < 12779 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999911 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12779 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12780 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12780. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12780 : WorldParameters where
  hiddenCharge := (73036343 / 62500000000 : ℝ)
  frame := (624526305069 / 1000000000000 : ℝ)
  moment := (4639419771 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12780 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472892050263 / 1000000000000 : ℝ)
    root := (8441571987 / 1000000000000 : ℝ) }

noncomputable def scalar12780 : ScalarCertificate 12780 world12780 agent12780 where
  dimensionLo := 12780
  dimensionHi := 12780
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2206714599 / 1000000000000 : ℝ)
  frameLo := (624526305069 / 1000000000000 : ℝ)
  frameHi := (1472892050263 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12780]
  agentFrame_pos := by norm_num only [agent12780]
  worldRadius := (2206714599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12780]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1360575817 / 1000000000000 : ℝ)
  lowerTail := (807719359 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3924604281 / 500000000000 : ℝ)
  ledger := by
    have h : (73036343 / 62500000000 : ℚ) +
        (4639419771 / 500000000000000000 : ℚ) / (2206714599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1360575817 / 1000000000000 : ℚ) + (807719359 / 500000000000 : ℚ) ≤
        (3924604281 / 500000000000 : ℚ) := by norm_num only
    have hc : (((73036343 / 62500000000 : ℚ) +
        (4639419771 / 500000000000000000 : ℚ) / (2206714599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1360575817 / 1000000000000 : ℚ) + (807719359 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3924604281 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12780]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12780 :
    2 * 160 < 12780 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999723 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12780 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12781 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12781. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12781 : WorldParameters where
  hiddenCharge := (584269399 / 500000000000 : ℝ)
  frame := (312256319381 / 500000000000 : ℝ)
  moment := (4638471381 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12781 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (184107612603 / 125000000000 : ℝ)
    root := (8440906093 / 1000000000000 : ℝ) }

noncomputable def scalar12781 : ScalarCertificate 12781 world12781 agent12781 where
  dimensionLo := 12781
  dimensionHi := 12781
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2207072899 / 1000000000000 : ℝ)
  frameLo := (312256319381 / 500000000000 : ℝ)
  frameHi := (184107612603 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12781]
  agentFrame_pos := by norm_num only [agent12781]
  worldRadius := (2207072899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12781]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (42482347 / 31250000000 : ℝ)
  lowerTail := (807090579 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1961439897 / 250000000000 : ℝ)
  ledger := by
    have h : (584269399 / 500000000000 : ℚ) +
        (4638471381 / 500000000000000000 : ℚ) / (2207072899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (42482347 / 31250000000 : ℚ) + (807090579 / 500000000000 : ℚ) ≤
        (1961439897 / 250000000000 : ℚ) := by norm_num only
    have hc : (((584269399 / 500000000000 : ℚ) +
        (4638471381 / 500000000000000000 : ℚ) / (2207072899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (42482347 / 31250000000 : ℚ) + (807090579 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1961439897 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12781]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12781 :
    2 * 160 < 12781 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999297 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12781 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12782 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12782. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12782 : WorldParameters where
  hiddenCharge := (1168496119 / 1000000000000 : ℝ)
  frame := (624498974631 / 1000000000000 : ℝ)
  moment := (371001861 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12782 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472829764919 / 1000000000000 : ℝ)
    root := (8440240401 / 1000000000000 : ℝ) }

noncomputable def scalar12782 : ScalarCertificate 12782 world12782 agent12782 where
  dimensionLo := 12782
  dimensionHi := 12782
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2207431299 / 1000000000000 : ℝ)
  frameLo := (624498974631 / 1000000000000 : ℝ)
  frameHi := (1472829764919 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12782]
  agentFrame_pos := by norm_num only [agent12782]
  worldRadius := (2207431299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12782]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (84893473 / 62500000000 : ℝ)
  lowerTail := (806462413 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7842313521 / 1000000000000 : ℝ)
  ledger := by
    have h : (1168496119 / 1000000000000 : ℚ) +
        (371001861 / 40000000000000000 : ℚ) / (2207431299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (84893473 / 62500000000 : ℚ) + (806462413 / 500000000000 : ℚ) ≤
        (7842313521 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1168496119 / 1000000000000 : ℚ) +
        (371001861 / 40000000000000000 : ℚ) / (2207431299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (84893473 / 62500000000 : ℚ) + (806462413 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7842313521 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12782]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12782 :
    2 * 160 < 12782 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997683 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12782 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12783 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12783. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12783 : WorldParameters where
  hiddenCharge := (1168453451 / 1000000000000 : ℝ)
  frame := (24979412507 / 40000000000 : ℝ)
  moment := (2318287707 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12783 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472798648437 / 1000000000000 : ℝ)
    root := (131868359 / 15625000000 : ℝ) }

noncomputable def scalar12783 : ScalarCertificate 12783 world12783 agent12783 where
  dimensionLo := 12783
  dimensionHi := 12783
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2207789599 / 1000000000000 : ℝ)
  frameLo := (24979412507 / 40000000000 : ℝ)
  frameHi := (1472798648437 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12783]
  agentFrame_pos := by norm_num only [agent12783]
  worldRadius := (2207789599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12783]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1357157123 / 1000000000000 : ℝ)
  lowerTail := (1611669623 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3919435261 / 500000000000 : ℝ)
  ledger := by
    have h : (1168453451 / 1000000000000 : ℚ) +
        (2318287707 / 250000000000000000 : ℚ) / (2207789599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1357157123 / 1000000000000 : ℚ) + (1611669623 / 1000000000000 : ℚ) ≤
        (3919435261 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1168453451 / 1000000000000 : ℚ) +
        (2318287707 / 250000000000000000 : ℚ) / (2207789599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1357157123 / 1000000000000 : ℚ) + (1611669623 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3919435261 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12783]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12783 :
    2 * 160 < 12783 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997491 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12783 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12784 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12784. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12784 : WorldParameters where
  hiddenCharge := (584205397 / 500000000000 : ℝ)
  frame := (624471652893 / 1000000000000 : ℝ)
  moment := (4635627837 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12784 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472767545473 / 1000000000000 : ℝ)
    root := (8438909687 / 1000000000000 : ℝ) }

noncomputable def scalar12784 : ScalarCertificate 12784 world12784 agent12784 where
  dimensionLo := 12784
  dimensionHi := 12784
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2208147899 / 1000000000000 : ℝ)
  frameLo := (624471652893 / 1000000000000 : ℝ)
  frameHi := (1472767545473 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12784]
  agentFrame_pos := by norm_num only [agent12784]
  worldRadius := (2208147899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12784]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1356019719 / 1000000000000 : ℝ)
  lowerTail := (1610415501 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7835430321 / 1000000000000 : ℝ)
  ledger := by
    have h : (584205397 / 500000000000 : ℚ) +
        (4635627837 / 500000000000000000 : ℚ) / (2208147899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1356019719 / 1000000000000 : ℚ) + (1610415501 / 1000000000000 : ℚ) ≤
        (7835430321 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((584205397 / 500000000000 : ℚ) +
        (4635627837 / 500000000000000000 : ℚ) / (2208147899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1356019719 / 1000000000000 : ℚ) + (1610415501 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7835430321 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12784]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12784 :
    2 * 160 < 12784 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995269 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12784 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12785 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12785. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12785 : WorldParameters where
  hiddenCharge := (292092037 / 250000000000 : ℝ)
  frame := (124891599057 / 200000000000 : ℝ)
  moment := (463468053 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12785 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472736456017 / 1000000000000 : ℝ)
    root := (1054780583 / 125000000000 : ℝ) }

noncomputable def scalar12785 : ScalarCertificate 12785 world12785 agent12785 where
  dimensionLo := 12785
  dimensionHi := 12785
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2208506199 / 1000000000000 : ℝ)
  frameLo := (124891599057 / 200000000000 : ℝ)
  frameHi := (1472736456017 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12785]
  agentFrame_pos := by norm_num only [agent12785]
  worldRadius := (2208506199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12785]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (67744173 / 50000000000 : ℝ)
  lowerTail := (321832513 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3915996563 / 500000000000 : ℝ)
  ledger := by
    have h : (292092037 / 250000000000 : ℚ) +
        (463468053 / 50000000000000000 : ℚ) / (2208506199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (67744173 / 50000000000 : ℚ) + (321832513 / 200000000000 : ℚ) ≤
        (3915996563 / 500000000000 : ℚ) := by norm_num only
    have hc : (((292092037 / 250000000000 : ℚ) +
        (463468053 / 50000000000000000 : ℚ) / (2208506199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (67744173 / 50000000000 : ℚ) + (321832513 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3915996563 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12785]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12785 :
    2 * 160 < 12785 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999631 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12785 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12786 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12786. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12786 : WorldParameters where
  hiddenCharge := (584162757 / 500000000000 : ℝ)
  frame := (156111084963 / 250000000000 : ℝ)
  moment := (2316866747 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12786 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472705385959 / 1000000000000 : ℝ)
    root := (4218789889 / 500000000000 : ℝ) }

noncomputable def scalar12786 : ScalarCertificate 12786 world12786 agent12786 where
  dimensionLo := 12786
  dimensionHi := 12786
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2208864599 / 1000000000000 : ℝ)
  frameLo := (156111084963 / 250000000000 : ℝ)
  frameHi := (1472705385959 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12786]
  agentFrame_pos := by norm_num only [agent12786]
  worldRadius := (2208864599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12786]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (270749669 / 200000000000 : ℝ)
  lowerTail := (1607910827 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7828558777 / 1000000000000 : ℝ)
  ledger := by
    have h : (584162757 / 500000000000 : ℚ) +
        (2316866747 / 250000000000000000 : ℚ) / (2208864599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (270749669 / 200000000000 : ℚ) + (1607910827 / 1000000000000 : ℚ) ≤
        (7828558777 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((584162757 / 500000000000 : ℚ) +
        (2316866747 / 250000000000000000 : ℚ) / (2208864599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (270749669 / 200000000000 : ℚ) + (1607910827 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7828558777 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12786]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12786 :
    2 * 160 < 12786 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999703 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12786 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12787 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12787. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12787 : WorldParameters where
  hiddenCharge := (1168282891 / 1000000000000 : ℝ)
  frame := (624430686591 / 1000000000000 : ℝ)
  moment := (579098341 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12787 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472674193777 / 1000000000000 : ℝ)
    root := (2109228773 / 250000000000 : ℝ) }

noncomputable def scalar12787 : ScalarCertificate 12787 world12787 agent12787 where
  dimensionLo := 12787
  dimensionHi := 12787
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2209223099 / 1000000000000 : ℝ)
  frameLo := (624430686591 / 1000000000000 : ℝ)
  frameHi := (1472674193777 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12787]
  agentFrame_pos := by norm_num only [agent12787]
  worldRadius := (2209223099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12787]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (270522767 / 200000000000 : ℝ)
  lowerTail := (803329803 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7825126051 / 1000000000000 : ℝ)
  ledger := by
    have h : (1168282891 / 1000000000000 : ℚ) +
        (579098341 / 62500000000000000 : ℚ) / (2209223099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (270522767 / 200000000000 : ℚ) + (803329803 / 500000000000 : ℚ) ≤
        (7825126051 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1168282891 / 1000000000000 : ℚ) +
        (579098341 / 62500000000000000 : ℚ) / (2209223099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (270522767 / 200000000000 : ℚ) + (803329803 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7825126051 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12787]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12787 :
    2 * 160 < 12787 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997261 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12787 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12788 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12788. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12788 : WorldParameters where
  hiddenCharge := (1168240279 / 1000000000000 : ℝ)
  frame := (312208517751 / 500000000000 : ℝ)
  moment := (1852736093 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12788 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736321416153 / 500000000000 : ℝ)
    root := (8436250673 / 1000000000000 : ℝ) }

noncomputable def scalar12788 : ScalarCertificate 12788 world12788 agent12788 where
  dimensionLo := 12788
  dimensionHi := 12788
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2209581899 / 1000000000000 : ℝ)
  frameLo := (312208517751 / 500000000000 : ℝ)
  frameHi := (736321416153 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12788]
  agentFrame_pos := by norm_num only [agent12788]
  worldRadius := (2209581899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12788]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (27029599 / 20000000000 : ℝ)
  lowerTail := (1605408893 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3910847307 / 500000000000 : ℝ)
  ledger := by
    have h : (1168240279 / 1000000000000 : ℚ) +
        (1852736093 / 200000000000000000 : ℚ) / (2209581899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (27029599 / 20000000000 : ℚ) + (1605408893 / 1000000000000 : ℚ) ≤
        (3910847307 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1168240279 / 1000000000000 : ℚ) +
        (1852736093 / 200000000000000000 : ℚ) / (2209581899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (27029599 / 20000000000 : ℚ) + (1605408893 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3910847307 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12788]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12788 :
    2 * 160 < 12788 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (687499951 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12788 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12789 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12789. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12789 : WorldParameters where
  hiddenCharge := (1168197679 / 1000000000000 : ℝ)
  frame := (312201693293 / 500000000000 : ℝ)
  moment := (4630894007 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12789 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368152872557 / 250000000000 : ℝ)
    root := (2108896597 / 250000000000 : ℝ) }

noncomputable def scalar12789 : ScalarCertificate 12789 world12789 agent12789 where
  dimensionLo := 12789
  dimensionHi := 12789
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2209940599 / 1000000000000 : ℝ)
  frameLo := (312201693293 / 500000000000 : ℝ)
  frameHi := (368152872557 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12789]
  agentFrame_pos := by norm_num only [agent12789]
  worldRadius := (2209940599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12789]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1350347043 / 1000000000000 : ℝ)
  lowerTail := (320831839 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7818266019 / 1000000000000 : ℝ)
  ledger := by
    have h : (1168197679 / 1000000000000 : ℚ) +
        (4630894007 / 500000000000000000 : ℚ) / (2209940599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1350347043 / 1000000000000 : ℚ) + (320831839 / 200000000000 : ℚ) ≤
        (7818266019 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1168197679 / 1000000000000 : ℚ) +
        (4630894007 / 500000000000000000 : ℚ) / (2209940599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1350347043 / 1000000000000 : ℚ) + (320831839 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7818266019 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12789]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12789 :
    2 * 160 < 12789 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998913 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12789 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12790 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12790. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12790 : WorldParameters where
  hiddenCharge := (1168155089 / 1000000000000 : ℝ)
  frame := (1951217937 / 3125000000 : ℝ)
  moment := (9259896103 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12790 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472499877219 / 1000000000000 : ℝ)
    root := (8434922371 / 1000000000000 : ℝ) }

noncomputable def scalar12790 : ScalarCertificate 12790 world12790 agent12790 where
  dimensionLo := 12790
  dimensionHi := 12790
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2210412999 / 1000000000000 : ℝ)
  frameLo := (1951217937 / 3125000000 : ℝ)
  frameHi := (1472499877219 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12790]
  agentFrame_pos := by norm_num only [agent12790]
  worldRadius := (2210412999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12790]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (674486689 / 500000000000 : ℝ)
  lowerTail := (1602597431 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3907045141 / 500000000000 : ℝ)
  ledger := by
    have h : (1168155089 / 1000000000000 : ℚ) +
        (9259896103 / 1000000000000000000 : ℚ) / (2210412999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (674486689 / 500000000000 : ℚ) + (1602597431 / 1000000000000 : ℚ) ≤
        (3907045141 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1168155089 / 1000000000000 : ℚ) +
        (9259896103 / 1000000000000000000 : ℚ) / (2210412999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (674486689 / 500000000000 : ℚ) + (1602597431 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3907045141 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12790]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12790 :
    2 * 160 < 12790 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996323 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12790 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12791 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12791. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12791 : WorldParameters where
  hiddenCharge := (1168112511 / 1000000000000 : ℝ)
  frame := (312188047633 / 500000000000 : ℝ)
  moment := (9258004733 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12791 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (73623428447 / 50000000000 : ℝ)
    root := (1054282311 / 125000000000 : ℝ) }

noncomputable def scalar12791 : ScalarCertificate 12791 world12791 agent12791 where
  dimensionLo := 12791
  dimensionHi := 12791
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2210771799 / 1000000000000 : ℝ)
  frameLo := (312188047633 / 500000000000 : ℝ)
  frameHi := (73623428447 / 50000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12791]
  agentFrame_pos := by norm_num only [agent12791]
  worldRadius := (2210771799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12791]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1347842919 / 1000000000000 : ℝ)
  lowerTail := (160135031 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7810668021 / 1000000000000 : ℝ)
  ledger := by
    have h : (1168112511 / 1000000000000 : ℚ) +
        (9258004733 / 1000000000000000000 : ℚ) / (2210771799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1347842919 / 1000000000000 : ℚ) + (160135031 / 100000000000 : ℚ) ≤
        (7810668021 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1168112511 / 1000000000000 : ℚ) +
        (9258004733 / 1000000000000000000 : ℚ) / (2210771799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1347842919 / 1000000000000 : ℚ) + (160135031 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7810668021 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12791]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12791 :
    2 * 160 < 12791 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998781 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12791 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12792 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12792. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12792 : WorldParameters where
  hiddenCharge := (146008743 / 125000000000 : ℝ)
  frame := (312181226431 / 500000000000 : ℝ)
  moment := (4628056951 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12792 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58897491201 / 40000000000 : ℝ)
    root := (1686718961 / 200000000000 : ℝ) }

noncomputable def scalar12792 : ScalarCertificate 12792 world12792 agent12792 where
  dimensionLo := 12792
  dimensionHi := 12792
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2211130599 / 1000000000000 : ℝ)
  frameLo := (312181226431 / 500000000000 : ℝ)
  frameHi := (58897491201 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12792]
  agentFrame_pos := by norm_num only [agent12792]
  worldRadius := (2211130599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12792]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (134671357 / 100000000000 : ℝ)
  lowerTail := (800052173 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7807248697 / 1000000000000 : ℝ)
  ledger := by
    have h : (146008743 / 125000000000 : ℚ) +
        (4628056951 / 500000000000000000 : ℚ) / (2211130599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (134671357 / 100000000000 : ℚ) + (800052173 / 500000000000 : ℚ) ≤
        (7807248697 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((146008743 / 125000000000 : ℚ) +
        (4628056951 / 500000000000000000 : ℚ) / (2211130599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (134671357 / 100000000000 : ℚ) + (800052173 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7807248697 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12792]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12792 :
    2 * 160 < 12792 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999293 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12792 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12793 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12793. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12793 : WorldParameters where
  hiddenCharge := (292006847 / 250000000000 : ℝ)
  frame := (624348812627 / 1000000000000 : ℝ)
  moment := (925422361 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12793 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368101501143 / 250000000000 : ℝ)
    root := (8432931389 / 1000000000000 : ℝ) }

noncomputable def scalar12793 : ScalarCertificate 12793 world12793 agent12793 where
  dimensionLo := 12793
  dimensionHi := 12793
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2211489499 / 1000000000000 : ℝ)
  frameLo := (624348812627 / 1000000000000 : ℝ)
  frameHi := (368101501143 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12793]
  agentFrame_pos := by norm_num only [agent12793]
  worldRadius := (2211489499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12793]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (672792719 / 500000000000 : ℝ)
  lowerTail := (31977193 / 20000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7803832359 / 1000000000000 : ℝ)
  ledger := by
    have h : (292006847 / 250000000000 : ℚ) +
        (925422361 / 100000000000000000 : ℚ) / (2211489499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (672792719 / 500000000000 : ℚ) + (31977193 / 20000000000 : ℚ) ≤
        (7803832359 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((292006847 / 250000000000 : ℚ) +
        (925422361 / 100000000000000000 : ℚ) / (2211489499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (672792719 / 500000000000 : ℚ) + (31977193 / 20000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7803832359 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12793]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12793 :
    2 * 160 < 12793 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (219999983 / 20000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12793 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12794 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12794. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12794 : WorldParameters where
  hiddenCharge := (1167984843 / 1000000000000 : ℝ)
  frame := (312167587281 / 500000000000 : ℝ)
  moment := (9252333859 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12794 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (294474949693 / 200000000000 : ℝ)
    root := (4216134053 / 500000000000 : ℝ) }

noncomputable def scalar12794 : ScalarCertificate 12794 world12794 agent12794 where
  dimensionLo := 12794
  dimensionHi := 12794
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2211848299 / 1000000000000 : ℝ)
  frameLo := (312167587281 / 500000000000 : ℝ)
  frameHi := (294474949693 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12794]
  agentFrame_pos := by norm_num only [agent12794]
  worldRadius := (2211848299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12794]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1344458279 / 1000000000000 : ℝ)
  lowerTail := (399403991 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (243763089 / 31250000000 : ℝ)
  ledger := by
    have h : (1167984843 / 1000000000000 : ℚ) +
        (9252333859 / 1000000000000000000 : ℚ) / (2211848299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1344458279 / 1000000000000 : ℚ) + (399403991 / 250000000000 : ℚ) ≤
        (243763089 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1167984843 / 1000000000000 : ℚ) +
        (9252333859 / 1000000000000000000 : ℚ) / (2211848299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1344458279 / 1000000000000 : ℚ) + (399403991 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((243763089 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12794]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12794 :
    2 * 160 < 12794 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999447 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12794 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12795 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12795. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12795 : WorldParameters where
  hiddenCharge := (1167942309 / 1000000000000 : ℝ)
  frame := (124864307733 / 200000000000 : ℝ)
  moment := (4625222323 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12795 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472343511697 / 1000000000000 : ℝ)
    root := (263487657 / 31250000000 : ℝ) }

noncomputable def scalar12795 : ScalarCertificate 12795 world12795 agent12795 where
  dimensionLo := 12795
  dimensionHi := 12795
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2212207199 / 1000000000000 : ℝ)
  frameLo := (124864307733 / 200000000000 : ℝ)
  frameHi := (1472343511697 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12795]
  agentFrame_pos := by norm_num only [agent12795]
  worldRadius := (2212207199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12795]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (335833077 / 250000000000 : ℝ)
  lowerTail := (19954669 / 12500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1559401653 / 200000000000 : ℝ)
  ledger := by
    have h : (1167942309 / 1000000000000 : ℚ) +
        (4625222323 / 500000000000000000 : ℚ) / (2212207199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (335833077 / 250000000000 : ℚ) + (19954669 / 12500000000 : ℚ) ≤
        (1559401653 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1167942309 / 1000000000000 : ℚ) +
        (4625222323 / 500000000000000000 : ℚ) / (2212207199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (335833077 / 250000000000 : ℚ) + (19954669 / 12500000000 : ℚ) : ℚ) : ℝ) ≤
        ((1559401653 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12795]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12795 :
    2 * 160 < 12795 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997329 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12795 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12796 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12796. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12796 : WorldParameters where
  hiddenCharge := (1167899787 / 1000000000000 : ℝ)
  frame := (78038488117 / 125000000000 : ℝ)
  moment := (2312138993 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12796 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472312288363 / 1000000000000 : ℝ)
    root := (8430942207 / 1000000000000 : ℝ) }

noncomputable def scalar12796 : ScalarCertificate 12796 world12796 agent12796 where
  dimensionLo := 12796
  dimensionHi := 12796
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2212566099 / 1000000000000 : ℝ)
  frameLo := (78038488117 / 125000000000 : ℝ)
  frameHi := (1472312288363 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12796]
  agentFrame_pos := by norm_num only [agent12796]
  worldRadius := (2212566099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12796]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1342207469 / 1000000000000 : ℝ)
  lowerTail := (1595132251 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7793600659 / 1000000000000 : ℝ)
  ledger := by
    have h : (1167899787 / 1000000000000 : ℚ) +
        (2312138993 / 250000000000000000 : ℚ) / (2212566099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1342207469 / 1000000000000 : ℚ) + (1595132251 / 1000000000000 : ℚ) ≤
        (7793600659 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1167899787 / 1000000000000 : ℚ) +
        (2312138993 / 250000000000000000 : ℚ) / (2212566099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1342207469 / 1000000000000 : ℚ) + (1595132251 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7793600659 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12796]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12796 :
    2 * 160 < 12796 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999461 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12796 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12797 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12797. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12797 : WorldParameters where
  hiddenCharge := (291964319 / 250000000000 : ℝ)
  frame := (4994354187 / 8000000000 : ℝ)
  moment := (9246667837 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12797 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472281084351 / 1000000000000 : ℝ)
    root := (337211181 / 40000000000 : ℝ) }

noncomputable def scalar12797 : ScalarCertificate 12797 world12797 agent12797 where
  dimensionLo := 12797
  dimensionHi := 12797
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2212924899 / 1000000000000 : ℝ)
  frameLo := (4994354187 / 8000000000 : ℝ)
  frameHi := (1472281084351 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12797]
  agentFrame_pos := by norm_num only [agent12797]
  worldRadius := (2212924899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12797]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1341083599 / 1000000000000 : ℝ)
  lowerTail := (398472997 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (779019587 / 100000000000 : ℝ)
  ledger := by
    have h : (291964319 / 250000000000 : ℚ) +
        (9246667837 / 1000000000000000000 : ℚ) / (2212924899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1341083599 / 1000000000000 : ℚ) + (398472997 / 250000000000 : ℚ) ≤
        (779019587 / 100000000000 : ℚ) := by norm_num only
    have hc : (((291964319 / 250000000000 : ℚ) +
        (9246667837 / 1000000000000000000 : ℚ) / (2212924899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1341083599 / 1000000000000 : ℚ) + (398472997 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((779019587 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12797]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12797 :
    2 * 160 < 12797 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (219999961 / 20000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12797 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12798 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12798. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12798 : WorldParameters where
  hiddenCharge := (145976847 / 125000000000 : ℝ)
  frame := (624280643981 / 1000000000000 : ℝ)
  moment := (9244780241 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12798 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (29444997993 / 20000000000 : ℝ)
    root := (4214808521 / 500000000000 : ℝ) }

noncomputable def scalar12798 : ScalarCertificate 12798 world12798 agent12798 where
  dimensionLo := 12798
  dimensionHi := 12798
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2213283699 / 1000000000000 : ℝ)
  frameLo := (624280643981 / 1000000000000 : ℝ)
  frameHi := (29444997993 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12798]
  agentFrame_pos := by norm_num only [agent12798]
  worldRadius := (2213283699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12798]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1339960831 / 1000000000000 : ℝ)
  lowerTail := (12741223 / 8000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7786794001 / 1000000000000 : ℝ)
  ledger := by
    have h : (145976847 / 125000000000 : ℚ) +
        (9244780241 / 1000000000000000000 : ℚ) / (2213283699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1339960831 / 1000000000000 : ℚ) + (12741223 / 8000000000 : ℚ) ≤
        (7786794001 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((145976847 / 125000000000 : ℚ) +
        (9244780241 / 1000000000000000000 : ℚ) / (2213283699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1339960831 / 1000000000000 : ℚ) + (12741223 / 8000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7786794001 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12798]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12798 :
    2 * 160 < 12798 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199998937 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12798 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12799 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12799. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12799 : WorldParameters where
  hiddenCharge := (1167772287 / 1000000000000 : ℝ)
  frame := (624267016753 / 1000000000000 : ℝ)
  moment := (9242893183 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12799 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472218728359 / 1000000000000 : ℝ)
    root := (1053619353 / 125000000000 : ℝ) }

noncomputable def scalar12799 : ScalarCertificate 12799 world12799 agent12799 where
  dimensionLo := 12799
  dimensionHi := 12799
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2213642599 / 1000000000000 : ℝ)
  frameLo := (624267016753 / 1000000000000 : ℝ)
  frameHi := (1472218728359 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12799]
  agentFrame_pos := by norm_num only [agent12799]
  worldRadius := (2213642599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12799]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1338839273 / 1000000000000 : ℝ)
  lowerTail := (795707511 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7783395099 / 1000000000000 : ℝ)
  ledger := by
    have h : (1167772287 / 1000000000000 : ℚ) +
        (9242893183 / 1000000000000000000 : ℚ) / (2213642599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1338839273 / 1000000000000 : ℚ) + (795707511 / 500000000000 : ℚ) ≤
        (7783395099 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1167772287 / 1000000000000 : ℚ) +
        (9242893183 / 1000000000000000000 : ℚ) / (2213642599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1338839273 / 1000000000000 : ℚ) + (795707511 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7783395099 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12799]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12799 :
    2 * 160 < 12799 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (137499937 / 12500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12799 {← IO.monoMsNow}" : IO Unit)
