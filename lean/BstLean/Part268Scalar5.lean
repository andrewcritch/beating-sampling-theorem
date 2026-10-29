import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12475 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12475. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12475 : WorldParameters where
  hiddenCharge := (295536247 / 250000000000 : ℝ)
  frame := (157199693199 / 250000000000 : ℝ)
  moment := (9883621259 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12475 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1485500758761 / 1000000000000 : ℝ)
    root := (8653759879 / 1000000000000 : ℝ) }

noncomputable def scalar12475 : ScalarCertificate 12475 world12475 agent12475 where
  dimensionLo := 12475
  dimensionHi := 12475
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2094896999 / 1000000000000 : ℝ)
  frameLo := (157199693199 / 250000000000 : ℝ)
  frameHi := (1485500758761 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12475]
  agentFrame_pos := by norm_num only [agent12475]
  worldRadius := (2094896999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12475]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1775134717 / 1000000000000 : ℝ)
  lowerTail := (2069982201 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4539261923 / 500000000000 : ℝ)
  ledger := by
    have h : (295536247 / 250000000000 : ℚ) +
        (9883621259 / 1000000000000000000 : ℚ) / (2094896999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1775134717 / 1000000000000 : ℚ) + (2069982201 / 1000000000000 : ℚ) ≤
        (4539261923 / 500000000000 : ℚ) := by norm_num only
    have hc : (((295536247 / 250000000000 : ℚ) +
        (9883621259 / 1000000000000000000 : ℚ) / (2094896999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1775134717 / 1000000000000 : ℚ) + (2069982201 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4539261923 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12475]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12475 :
    2 * 160 < 12475 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (34374999 / 3125000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12475 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12476 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12476. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12476 : WorldParameters where
  hiddenCharge := (236419737 / 200000000000 : ℝ)
  frame := (628784416139 / 1000000000000 : ℝ)
  moment := (9881549529 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12476 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (742732943347 / 500000000000 : ℝ)
    root := (865303547 / 100000000000 : ℝ) }

noncomputable def scalar12476 : ScalarCertificate 12476 world12476 agent12476 where
  dimensionLo := 12476
  dimensionHi := 12476
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2095248499 / 1000000000000 : ℝ)
  frameLo := (628784416139 / 1000000000000 : ℝ)
  frameHi := (742732943347 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12476]
  agentFrame_pos := by norm_num only [agent12476]
  worldRadius := (2095248499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12476]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (443398839 / 250000000000 : ℝ)
  lowerTail := (103415707 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9074042637 / 1000000000000 : ℝ)
  ledger := by
    have h : (236419737 / 200000000000 : ℚ) +
        (9881549529 / 1000000000000000000 : ℚ) / (2095248499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (443398839 / 250000000000 : ℚ) + (103415707 / 50000000000 : ℚ) ≤
        (9074042637 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((236419737 / 200000000000 : ℚ) +
        (9881549529 / 1000000000000000000 : ℚ) / (2095248499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (443398839 / 250000000000 : ℚ) + (103415707 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9074042637 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12476]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12476 :
    2 * 160 < 12476 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997373 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12476 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12477 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12477. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12477 : WorldParameters where
  hiddenCharge := (236410479 / 200000000000 : ℝ)
  frame := (157192515459 / 250000000000 : ℝ)
  moment := (4939739203 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12477 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (59417241011 / 40000000000 : ℝ)
    root := (8652311291 / 1000000000000 : ℝ) }

noncomputable def scalar12477 : ScalarCertificate 12477 world12477 agent12477 where
  dimensionLo := 12477
  dimensionHi := 12477
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2095600099 / 1000000000000 : ℝ)
  frameLo := (157192515459 / 250000000000 : ℝ)
  frameHi := (59417241011 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12477]
  agentFrame_pos := by norm_num only [agent12477]
  worldRadius := (2095600099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12477]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (886028799 / 500000000000 : ℝ)
  lowerTail := (413329543 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9069565303 / 1000000000000 : ℝ)
  ledger := by
    have h : (236410479 / 200000000000 : ℚ) +
        (4939739203 / 500000000000000000 : ℚ) / (2095600099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (886028799 / 500000000000 : ℚ) + (413329543 / 200000000000 : ℚ) ≤
        (9069565303 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((236410479 / 200000000000 : ℚ) +
        (4939739203 / 500000000000000000 : ℚ) / (2095600099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (886028799 / 500000000000 : ℚ) + (413329543 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9069565303 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12477]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12477 :
    2 * 160 < 12477 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999973 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12477 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12478 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12478. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12478 : WorldParameters where
  hiddenCharge := (1182006117 / 1000000000000 : ℝ)
  frame := (314377854943 / 500000000000 : ℝ)
  moment := (9877407889 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12478 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1485396192401 / 1000000000000 : ℝ)
    root := (2162896853 / 250000000000 : ℝ) }

noncomputable def scalar12478 : ScalarCertificate 12478 world12478 agent12478 where
  dimensionLo := 12478
  dimensionHi := 12478
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2095951799 / 1000000000000 : ℝ)
  frameLo := (314377854943 / 500000000000 : ℝ)
  frameHi := (1485396192401 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12478]
  agentFrame_pos := by norm_num only [agent12478]
  worldRadius := (2095951799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12478]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (885260803 / 500000000000 : ℝ)
  lowerTail := (516245777 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1813018437 / 200000000000 : ℝ)
  ledger := by
    have h : (1182006117 / 1000000000000 : ℚ) +
        (9877407889 / 1000000000000000000 : ℚ) / (2095951799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (885260803 / 500000000000 : ℚ) + (516245777 / 250000000000 : ℚ) ≤
        (1813018437 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1182006117 / 1000000000000 : ℚ) +
        (9877407889 / 1000000000000000000 : ℚ) / (2095951799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (885260803 / 500000000000 : ℚ) + (516245777 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1813018437 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12478]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12478 :
    2 * 160 < 12478 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998569 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12478 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12479 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12479. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12479 : WorldParameters where
  hiddenCharge := (1181959851 / 1000000000000 : ℝ)
  frame := (19648167509 / 31250000000 : ℝ)
  moment := (9875337979 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12479 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (37134034403 / 25000000000 : ℝ)
    root := (4325431847 / 500000000000 : ℝ) }

noncomputable def scalar12479 : ScalarCertificate 12479 world12479 agent12479 where
  dimensionLo := 12479
  dimensionHi := 12479
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2096303399 / 1000000000000 : ℝ)
  frameLo := (19648167509 / 31250000000 : ℝ)
  frameHi := (37134034403 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12479]
  agentFrame_pos := by norm_num only [agent12479]
  worldRadius := (2096303399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12479]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1768986967 / 1000000000000 : ℝ)
  lowerTail := (1031659939 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9060622857 / 1000000000000 : ℝ)
  ledger := by
    have h : (1181959851 / 1000000000000 : ℚ) +
        (9875337979 / 1000000000000000000 : ℚ) / (2096303399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1768986967 / 1000000000000 : ℚ) + (1031659939 / 500000000000 : ℚ) ≤
        (9060622857 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1181959851 / 1000000000000 : ℚ) +
        (9875337979 / 1000000000000000000 : ℚ) / (2096303399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1768986967 / 1000000000000 : ℚ) + (1031659939 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9060622857 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12479]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12479 :
    2 * 160 < 12479 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999587 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12479 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12480 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12480. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12480 : WorldParameters where
  hiddenCharge := (1181913599 / 1000000000000 : ℝ)
  frame := (314363506521 / 500000000000 : ℝ)
  moment := (4936634337 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12480 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1485242587511 / 1000000000000 : ℝ)
    root := (4325070137 / 500000000000 : ℝ) }

noncomputable def scalar12480 : ScalarCertificate 12480 world12480 agent12480 where
  dimensionLo := 12480
  dimensionHi := 12480
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2096764099 / 1000000000000 : ℝ)
  frameLo := (314363506521 / 500000000000 : ℝ)
  frameHi := (1485242587511 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12480]
  agentFrame_pos := by norm_num only [agent12480]
  worldRadius := (2096764099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12480]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1767129899 / 1000000000000 : ℝ)
  lowerTail := (2061247151 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4527594363 / 500000000000 : ℝ)
  ledger := by
    have h : (1181913599 / 1000000000000 : ℚ) +
        (4936634337 / 500000000000000000 : ℚ) / (2096764099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1767129899 / 1000000000000 : ℚ) + (2061247151 / 1000000000000 : ℚ) ≤
        (4527594363 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1181913599 / 1000000000000 : ℚ) +
        (4936634337 / 500000000000000000 : ℚ) / (2096764099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1767129899 / 1000000000000 : ℚ) + (2061247151 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4527594363 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12480]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12480 :
    2 * 160 < 12480 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999751 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12480 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12481 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12481. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12481 : WorldParameters where
  hiddenCharge := (590933679 / 500000000000 : ℝ)
  frame := (157178167037 / 250000000000 : ℝ)
  moment := (1233899997 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12481 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (742603908669 / 500000000000 : ℝ)
    root := (1729883403 / 200000000000 : ℝ) }

noncomputable def scalar12481 : ScalarCertificate 12481 world12481 agent12481 where
  dimensionLo := 12481
  dimensionHi := 12481
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2097115799 / 1000000000000 : ℝ)
  frameLo := (157178167037 / 250000000000 : ℝ)
  frameHi := (742603908669 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12481]
  agentFrame_pos := by norm_num only [agent12481]
  worldRadius := (2097115799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12481]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (110349919 / 62500000000 : ℝ)
  lowerTail := (205958749 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1810145611 / 200000000000 : ℝ)
  ledger := by
    have h : (590933679 / 500000000000 : ℚ) +
        (1233899997 / 125000000000000000 : ℚ) / (2097115799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (110349919 / 62500000000 : ℚ) + (205958749 / 100000000000 : ℚ) ≤
        (1810145611 / 200000000000 : ℚ) := by norm_num only
    have hc : (((590933679 / 500000000000 : ℚ) +
        (1233899997 / 125000000000000000 : ℚ) / (2097115799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (110349919 / 62500000000 : ℚ) + (205958749 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1810145611 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12481]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12481 :
    2 * 160 < 12481 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998649 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12481 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12482 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12482. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12482 : WorldParameters where
  hiddenCharge := (118182113 / 100000000000 : ℝ)
  frame := (157174581401 / 250000000000 : ℝ)
  moment := (9869131883 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12482 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (37129326593 / 25000000000 : ℝ)
    root := (1729738811 / 200000000000 : ℝ) }

noncomputable def scalar12482 : ScalarCertificate 12482 world12482 agent12482 where
  dimensionLo := 12482
  dimensionHi := 12482
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2097467499 / 1000000000000 : ℝ)
  frameLo := (157174581401 / 250000000000 : ℝ)
  frameHi := (37129326593 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12482]
  agentFrame_pos := by norm_num only [agent12482]
  worldRadius := (2097467499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12482]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1764069103 / 1000000000000 : ℝ)
  lowerTail := (514482363 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2261567861 / 250000000000 : ℝ)
  ledger := by
    have h : (118182113 / 100000000000 : ℚ) +
        (9869131883 / 1000000000000000000 : ℚ) / (2097467499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1764069103 / 1000000000000 : ℚ) + (514482363 / 250000000000 : ℚ) ≤
        (2261567861 / 250000000000 : ℚ) := by norm_num only
    have hc : (((118182113 / 100000000000 : ℚ) +
        (9869131883 / 1000000000000000000 : ℚ) / (2097467499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1764069103 / 1000000000000 : ℚ) + (514482363 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2261567861 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12482]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12482 :
    2 * 160 < 12482 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999131 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12482 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12483 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12483. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12483 : WorldParameters where
  hiddenCharge := (236354983 / 200000000000 : ℝ)
  frame := (62868398541 / 100000000000 : ℝ)
  moment := (1973412879 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12483 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (371284583153 / 250000000000 : ℝ)
    root := (4323985627 / 500000000000 : ℝ) }

noncomputable def scalar12483 : ScalarCertificate 12483 world12483 agent12483 where
  dimensionLo := 12483
  dimensionHi := 12483
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2097819099 / 1000000000000 : ℝ)
  frameLo := (62868398541 / 100000000000 : ℝ)
  frameHi := (371284583153 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12483]
  agentFrame_pos := by norm_num only [agent12483]
  worldRadius := (2097819099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12483]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (881270439 / 500000000000 : ℝ)
  lowerTail := (2056272821 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (361672747 / 40000000000 : ℝ)
  ledger := by
    have h : (236354983 / 200000000000 : ℚ) +
        (1973412879 / 200000000000000000 : ℚ) / (2097819099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (881270439 / 500000000000 : ℚ) + (2056272821 / 1000000000000 : ℚ) ≤
        (361672747 / 40000000000 : ℚ) := by norm_num only
    have hc : (((236354983 / 200000000000 : ℚ) +
        (1973412879 / 200000000000000000 : ℚ) / (2097819099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (881270439 / 500000000000 : ℚ) + (2056272821 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((361672747 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12483]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12483 :
    2 * 160 < 12483 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994587 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12483 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12484 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12484. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12484 : WorldParameters where
  hiddenCharge := (147716089 / 125000000000 : ℝ)
  frame := (314334823783 / 500000000000 : ℝ)
  moment := (1233124689 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12484 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (742551809017 / 500000000000 : ℝ)
    root := (4323624341 / 500000000000 : ℝ) }

noncomputable def scalar12484 : ScalarCertificate 12484 world12484 agent12484 where
  dimensionLo := 12484
  dimensionHi := 12484
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2098170799 / 1000000000000 : ℝ)
  frameLo := (314334823783 / 500000000000 : ℝ)
  frameHi := (742551809017 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12484]
  agentFrame_pos := by norm_num only [agent12484]
  worldRadius := (2098170799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12484]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (70440571 / 40000000000 : ℝ)
  lowerTail := (2054617851 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9037369817 / 1000000000000 : ℝ)
  ledger := by
    have h : (147716089 / 125000000000 : ℚ) +
        (1233124689 / 125000000000000000 : ℚ) / (2098170799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (70440571 / 40000000000 : ℚ) + (2054617851 / 1000000000000 : ℚ) ≤
        (9037369817 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((147716089 / 125000000000 : ℚ) +
        (1233124689 / 125000000000000000 : ℚ) / (2098170799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (70440571 / 40000000000 : ℚ) + (2054617851 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9037369817 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12484]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12484 :
    2 * 160 < 12484 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998723 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12484 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12485 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12485. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12485 : WorldParameters where
  hiddenCharge := (1181682521 / 1000000000000 : ℝ)
  frame := (62865531207 / 100000000000 : ℝ)
  moment := (1972586247 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12485 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (742534462971 / 500000000000 : ℝ)
    root := (8646526409 / 1000000000000 : ℝ) }

noncomputable def scalar12485 : ScalarCertificate 12485 world12485 agent12485 where
  dimensionLo := 12485
  dimensionHi := 12485
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2098522499 / 1000000000000 : ℝ)
  frameLo := (62865531207 / 100000000000 : ℝ)
  frameHi := (742534462971 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12485]
  agentFrame_pos := by norm_num only [agent12485]
  worldRadius := (2098522499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12485]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (175948929 / 100000000000 : ℝ)
  lowerTail := (2052964537 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9032925077 / 1000000000000 : ℝ)
  ledger := by
    have h : (1181682521 / 1000000000000 : ℚ) +
        (1972586247 / 200000000000000000 : ℚ) / (2098522499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (175948929 / 100000000000 : ℚ) + (2052964537 / 1000000000000 : ℚ) ≤
        (9032925077 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1181682521 / 1000000000000 : ℚ) +
        (1972586247 / 200000000000000000 : ℚ) / (2098522499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (175948929 / 100000000000 : ℚ) + (2052964537 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9032925077 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12485]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12485 :
    2 * 160 < 12485 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999063 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12485 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12486 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12486. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12486 : WorldParameters where
  hiddenCharge := (1181636343 / 1000000000000 : ℝ)
  frame := (628640978923 / 1000000000000 : ℝ)
  moment := (4930432781 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12486 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (742517128161 / 500000000000 : ℝ)
    root := (1729160859 / 200000000000 : ℝ) }

noncomputable def scalar12486 : ScalarCertificate 12486 world12486 agent12486 where
  dimensionLo := 12486
  dimensionHi := 12486
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2098873999 / 1000000000000 : ℝ)
  frameLo := (628640978923 / 1000000000000 : ℝ)
  frameHi := (742517128161 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12486]
  agentFrame_pos := by norm_num only [agent12486]
  worldRadius := (2098873999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12486]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (878982787 / 500000000000 : ℝ)
  lowerTail := (410262503 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2257121041 / 250000000000 : ℝ)
  ledger := by
    have h : (1181636343 / 1000000000000 : ℚ) +
        (4930432781 / 500000000000000000 : ℚ) / (2098873999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (878982787 / 500000000000 : ℚ) + (410262503 / 200000000000 : ℚ) ≤
        (2257121041 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1181636343 / 1000000000000 : ℚ) +
        (4930432781 / 500000000000000000 : ℚ) / (2098873999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (878982787 / 500000000000 : ℚ) + (410262503 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2257121041 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12486]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12486 :
    2 * 160 < 12486 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998301 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12486 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12487 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12487. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12487 : WorldParameters where
  hiddenCharge := (590795089 / 500000000000 : ℝ)
  frame := (628626648123 / 1000000000000 : ℝ)
  moment := (9858800493 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12487 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (742499801597 / 500000000000 : ℝ)
    root := (8645082479 / 1000000000000 : ℝ) }

noncomputable def scalar12487 : ScalarCertificate 12487 world12487 agent12487 where
  dimensionLo := 12487
  dimensionHi := 12487
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2099225699 / 1000000000000 : ℝ)
  frameLo := (628626648123 / 1000000000000 : ℝ)
  frameHi := (742499801597 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12487]
  agentFrame_pos := by norm_num only [agent12487]
  worldRadius := (2099225699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12487]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1756443647 / 1000000000000 : ℝ)
  lowerTail := (204966233 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9024047293 / 1000000000000 : ℝ)
  ledger := by
    have h : (590795089 / 500000000000 : ℚ) +
        (9858800493 / 1000000000000000000 : ℚ) / (2099225699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1756443647 / 1000000000000 : ℚ) + (204966233 / 100000000000 : ℚ) ≤
        (9024047293 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((590795089 / 500000000000 : ℚ) +
        (9858800493 / 1000000000000000000 : ℚ) / (2099225699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1756443647 / 1000000000000 : ℚ) + (204966233 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9024047293 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12487]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12487 :
    2 * 160 < 12487 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999733 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12487 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12488 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12488. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12488 : WorldParameters where
  hiddenCharge := (147693003 / 125000000000 : ℝ)
  frame := (62861231967 / 100000000000 : ℝ)
  moment := (9856736029 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12488 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1484964972513 / 1000000000000 : ℝ)
    root := (4322180411 / 500000000000 : ℝ) }

noncomputable def scalar12488 : ScalarCertificate 12488 world12488 agent12488 where
  dimensionLo := 12488
  dimensionHi := 12488
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2099577399 / 1000000000000 : ℝ)
  frameLo := (62861231967 / 100000000000 : ℝ)
  frameHi := (1484964972513 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12488]
  agentFrame_pos := by norm_num only [agent12488]
  worldRadius := (2099577399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12488]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (219365399 / 125000000000 : ℝ)
  lowerTail := (1024006827 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4509807121 / 500000000000 : ℝ)
  ledger := by
    have h : (147693003 / 125000000000 : ℚ) +
        (9856736029 / 1000000000000000000 : ℚ) / (2099577399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (219365399 / 125000000000 : ℚ) + (1024006827 / 500000000000 : ℚ) ≤
        (4509807121 / 500000000000 : ℚ) := by norm_num only
    have hc : (((147693003 / 125000000000 : ℚ) +
        (9856736029 / 1000000000000000000 : ℚ) / (2099577399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (219365399 / 125000000000 : ℚ) + (1024006827 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4509807121 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12488]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12488 :
    2 * 160 < 12488 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999503 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12488 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12489 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12489. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12489 : WorldParameters where
  hiddenCharge := (295374471 / 250000000000 : ℝ)
  frame := (157149498391 / 250000000000 : ℝ)
  moment := (9854672169 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12489 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1484930364267 / 1000000000000 : ℝ)
    root := (8643639393 / 1000000000000 : ℝ) }

noncomputable def scalar12489 : ScalarCertificate 12489 world12489 agent12489 where
  dimensionLo := 12489
  dimensionHi := 12489
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2099929099 / 1000000000000 : ℝ)
  frameLo := (157149498391 / 250000000000 : ℝ)
  frameHi := (1484930364267 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12489]
  agentFrame_pos := by norm_num only [agent12489]
  worldRadius := (2099929099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12489]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (438351069 / 250000000000 : ℝ)
  lowerTail := (2046366557 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9015185149 / 1000000000000 : ℝ)
  ledger := by
    have h : (295374471 / 250000000000 : ℚ) +
        (9854672169 / 1000000000000000000 : ℚ) / (2099929099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (438351069 / 250000000000 : ℚ) + (2046366557 / 1000000000000 : ℚ) ≤
        (9015185149 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((295374471 / 250000000000 : ℚ) +
        (9854672169 / 1000000000000000000 : ℚ) / (2099929099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (438351069 / 250000000000 : ℚ) + (2046366557 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9015185149 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12489]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12489 :
    2 * 160 < 12489 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998399 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12489 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12490 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12490. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12490 : WorldParameters where
  hiddenCharge := (236290351 / 200000000000 : ℝ)
  frame := (628583669803 / 1000000000000 : ℝ)
  moment := (615788057 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12490 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (742405950681 / 500000000000 : ℝ)
    root := (8642918263 / 1000000000000 : ℝ) }

noncomputable def scalar12490 : ScalarCertificate 12490 world12490 agent12490 where
  dimensionLo := 12490
  dimensionHi := 12490
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2100390099 / 1000000000000 : ℝ)
  frameLo := (628583669803 / 1000000000000 : ℝ)
  frameHi := (742405950681 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12490]
  agentFrame_pos := by norm_num only [agent12490]
  worldRadius := (2100390099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12490]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (437891499 / 250000000000 : ℝ)
  lowerTail := (2044313581 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9009799199 / 1000000000000 : ℝ)
  ledger := by
    have h : (236290351 / 200000000000 : ℚ) +
        (615788057 / 62500000000000000 : ℚ) / (2100390099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (437891499 / 250000000000 : ℚ) + (2044313581 / 1000000000000 : ℚ) ≤
        (9009799199 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((236290351 / 200000000000 : ℚ) +
        (615788057 / 62500000000000000 : ℚ) / (2100390099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (437891499 / 250000000000 : ℚ) + (2044313581 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9009799199 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12490]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12490 :
    2 * 160 < 12490 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998373 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12490 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12491 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12491. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12491 : WorldParameters where
  hiddenCharge := (1181405639 / 1000000000000 : ℝ)
  frame := (157142337097 / 250000000000 : ℝ)
  moment := (9850546259 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12491 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (296955466599 / 200000000000 : ℝ)
    root := (8642197291 / 1000000000000 : ℝ) }

noncomputable def scalar12491 : ScalarCertificate 12491 world12491 agent12491 where
  dimensionLo := 12491
  dimensionHi := 12491
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2100741899 / 1000000000000 : ℝ)
  frameLo := (157142337097 / 250000000000 : ℝ)
  frameHi := (296955466599 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12491]
  agentFrame_pos := by norm_num only [agent12491]
  worldRadius := (2100741899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12491]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (875025227 / 500000000000 : ℝ)
  lowerTail := (81706799 / 40000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9005378603 / 1000000000000 : ℝ)
  ledger := by
    have h : (1181405639 / 1000000000000 : ℚ) +
        (9850546259 / 1000000000000000000 : ℚ) / (2100741899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (875025227 / 500000000000 : ℚ) + (81706799 / 40000000000 : ℚ) ≤
        (9005378603 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1181405639 / 1000000000000 : ℚ) +
        (9850546259 / 1000000000000000000 : ℚ) / (2100741899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (875025227 / 500000000000 : ℚ) + (81706799 / 40000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9005378603 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12491]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12491 :
    2 * 160 < 12491 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999523 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12491 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12492 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12492. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12492 : WorldParameters where
  hiddenCharge := (73834971 / 62500000000 : ℝ)
  frame := (157138757329 / 250000000000 : ℝ)
  moment := (984848421 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12492 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (92796424189 / 62500000000 : ℝ)
    root := (4320738273 / 500000000000 : ℝ) }

noncomputable def scalar12492 : ScalarCertificate 12492 world12492 agent12492 where
  dimensionLo := 12492
  dimensionHi := 12492
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2101093599 / 1000000000000 : ℝ)
  frameLo := (157138757329 / 250000000000 : ℝ)
  frameHi := (92796424189 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12492]
  agentFrame_pos := by norm_num only [agent12492]
  worldRadius := (2101093599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12492]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (349707269 / 200000000000 : ℝ)
  lowerTail := (255128479 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9000961951 / 1000000000000 : ℝ)
  ledger := by
    have h : (73834971 / 62500000000 : ℚ) +
        (984848421 / 100000000000000000 : ℚ) / (2101093599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (349707269 / 200000000000 : ℚ) + (255128479 / 125000000000 : ℚ) ≤
        (9000961951 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((73834971 / 62500000000 : ℚ) +
        (984848421 / 100000000000000000 : ℚ) / (2101093599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (349707269 / 200000000000 : ℚ) + (255128479 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9000961951 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12492]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12492 :
    2 * 160 < 12492 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997249 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12492 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12493 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12493. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12493 : WorldParameters where
  hiddenCharge := (236262689 / 200000000000 : ℝ)
  frame := (628540712589 / 1000000000000 : ℝ)
  moment := (9846422763 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12493 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (148470825747 / 100000000000 : ℝ)
    root := (8640756099 / 1000000000000 : ℝ) }

noncomputable def scalar12493 : ScalarCertificate 12493 world12493 agent12493 where
  dimensionLo := 12493
  dimensionHi := 12493
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2101445299 / 1000000000000 : ℝ)
  frameLo := (628540712589 / 1000000000000 : ℝ)
  frameHi := (148470825747 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12493]
  agentFrame_pos := by norm_num only [agent12493]
  worldRadius := (2101445299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12493]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (27297247 / 15625000000 : ℝ)
  lowerTail := (2039387293 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8996549313 / 1000000000000 : ℝ)
  ledger := by
    have h : (236262689 / 200000000000 : ℚ) +
        (9846422763 / 1000000000000000000 : ℚ) / (2101445299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (27297247 / 15625000000 : ℚ) + (2039387293 / 1000000000000 : ℚ) ≤
        (8996549313 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((236262689 / 200000000000 : ℚ) +
        (9846422763 / 1000000000000000000 : ℚ) / (2101445299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (27297247 / 15625000000 : ℚ) + (2039387293 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8996549313 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12493]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12493 :
    2 * 160 < 12493 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995093 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12493 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12494 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12494. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12494 : WorldParameters where
  hiddenCharge := (590633683 / 500000000000 : ℝ)
  frame := (125705279641 / 200000000000 : ℝ)
  moment := (9844361919 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12494 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (742336872161 / 500000000000 : ℝ)
    root := (864003581 / 100000000000 : ℝ) }

noncomputable def scalar12494 : ScalarCertificate 12494 world12494 agent12494 where
  dimensionLo := 12494
  dimensionHi := 12494
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2101796999 / 1000000000000 : ℝ)
  frameLo := (125705279641 / 200000000000 : ℝ)
  frameHi := (742336872161 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12494]
  agentFrame_pos := by norm_num only [agent12494]
  worldRadius := (2101796999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12494]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1745512701 / 1000000000000 : ℝ)
  lowerTail := (2037748217 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4496070201 / 500000000000 : ℝ)
  ledger := by
    have h : (590633683 / 500000000000 : ℚ) +
        (9844361919 / 1000000000000000000 : ℚ) / (2101796999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1745512701 / 1000000000000 : ℚ) + (2037748217 / 1000000000000 : ℚ) ≤
        (4496070201 / 500000000000 : ℚ) := by norm_num only
    have hc : (((590633683 / 500000000000 : ℚ) +
        (9844361919 / 1000000000000000000 : ℚ) / (2101796999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1745512701 / 1000000000000 : ℚ) + (2037748217 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4496070201 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12494]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12494 :
    2 * 160 < 12494 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (549999969 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12494 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12495 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12495. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12495 : WorldParameters where
  hiddenCharge := (11812213 / 10000000000 : ℝ)
  frame := (157128021541 / 250000000000 : ℝ)
  moment := (4921150839 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12495 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (742319629749 / 500000000000 : ℝ)
    root := (2159828937 / 250000000000 : ℝ) }

noncomputable def scalar12495 : ScalarCertificate 12495 world12495 agent12495 where
  dimensionLo := 12495
  dimensionHi := 12495
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2102148799 / 1000000000000 : ℝ)
  frameLo := (157128021541 / 250000000000 : ℝ)
  frameHi := (742319629749 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12495]
  agentFrame_pos := by norm_num only [agent12495]
  worldRadius := (2102148799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12495]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (218000407 / 125000000000 : ℝ)
  lowerTail := (407222171 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2246933873 / 250000000000 : ℝ)
  ledger := by
    have h : (11812213 / 10000000000 : ℚ) +
        (4921150839 / 500000000000000000 : ℚ) / (2102148799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (218000407 / 125000000000 : ℚ) + (407222171 / 200000000000 : ℚ) ≤
        (2246933873 / 250000000000 : ℚ) := by norm_num only
    have hc : (((11812213 / 10000000000 : ℚ) +
        (4921150839 / 500000000000000000 : ℚ) / (2102148799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (218000407 / 125000000000 : ℚ) + (407222171 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2246933873 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12495]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12495 :
    2 * 160 < 12495 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998783 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12495 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12496 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12496. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12496 : WorldParameters where
  hiddenCharge := (590587623 / 500000000000 : ℝ)
  frame := (125699555293 / 200000000000 : ℝ)
  moment := (246006051 / 25000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12496 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (742302395527 / 500000000000 : ℝ)
    root := (539912249 / 62500000000 : ℝ) }

noncomputable def scalar12496 : ScalarCertificate 12496 world12496 agent12496 where
  dimensionLo := 12496
  dimensionHi := 12496
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2102500499 / 1000000000000 : ℝ)
  frameLo := (125699555293 / 200000000000 : ℝ)
  frameHi := (742302395527 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12496]
  agentFrame_pos := by norm_num only [agent12496]
  worldRadius := (2102500499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12496]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1742495277 / 1000000000000 : ℝ)
  lowerTail := (1017237491 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1122916823 / 125000000000 : ℝ)
  ledger := by
    have h : (590587623 / 500000000000 : ℚ) +
        (246006051 / 25000000000000000 : ℚ) / (2102500499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1742495277 / 1000000000000 : ℚ) + (1017237491 / 500000000000 : ℚ) ≤
        (1122916823 / 125000000000 : ℚ) := by norm_num only
    have hc : (((590587623 / 500000000000 : ℚ) +
        (246006051 / 25000000000000000 : ℚ) / (2102500499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1742495277 / 1000000000000 : ℚ) + (1017237491 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1122916823 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12496]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12496 :
    2 * 160 < 12496 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997263 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12496 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12497 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12497. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12497 : WorldParameters where
  hiddenCharge := (295282301 / 250000000000 : ℝ)
  frame := (628483469107 / 1000000000000 : ℝ)
  moment := (9838183003 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12497 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (742285169489 / 500000000000 : ℝ)
    root := (8637876377 / 1000000000000 : ℝ) }

noncomputable def scalar12497 : ScalarCertificate 12497 world12497 agent12497 where
  dimensionLo := 12497
  dimensionHi := 12497
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2102852299 / 1000000000000 : ℝ)
  frameLo := (628483469107 / 1000000000000 : ℝ)
  frameHi := (742285169489 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12497]
  agentFrame_pos := by norm_num only [agent12497]
  worldRadius := (2102852299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12497]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1740988823 / 1000000000000 : ℝ)
  lowerTail := (508210169 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (897893739 / 100000000000 : ℝ)
  ledger := by
    have h : (295282301 / 250000000000 : ℚ) +
        (9838183003 / 1000000000000000000 : ℚ) / (2102852299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1740988823 / 1000000000000 : ℚ) + (508210169 / 250000000000 : ℚ) ≤
        (897893739 / 100000000000 : ℚ) := by norm_num only
    have hc : (((295282301 / 250000000000 : ℚ) +
        (9838183003 / 1000000000000000000 : ℚ) / (2102852299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1740988823 / 1000000000000 : ℚ) + (508210169 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((897893739 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12497]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12497 :
    2 * 160 < 12497 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997541 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12497 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12498 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12498. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12498 : WorldParameters where
  hiddenCharge := (47243327 / 40000000000 : ℝ)
  frame := (628469164091 / 1000000000000 : ℝ)
  moment := (9836124569 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12498 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (185566988653 / 125000000000 : ℝ)
    root := (8637156997 / 1000000000000 : ℝ) }

noncomputable def scalar12498 : ScalarCertificate 12498 world12498 agent12498 where
  dimensionLo := 12498
  dimensionHi := 12498
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2103203999 / 1000000000000 : ℝ)
  frameLo := (628469164091 / 1000000000000 : ℝ)
  frameHi := (185566988653 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12498]
  agentFrame_pos := by norm_num only [agent12498]
  worldRadius := (2103203999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12498]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (108717737 / 62500000000 : ℝ)
  lowerTail := (2031207823 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2243636029 / 250000000000 : ℝ)
  ledger := by
    have h : (47243327 / 40000000000 : ℚ) +
        (9836124569 / 1000000000000000000 : ℚ) / (2103203999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (108717737 / 62500000000 : ℚ) + (2031207823 / 1000000000000 : ℚ) ≤
        (2243636029 / 250000000000 : ℚ) := by norm_num only
    have hc : (((47243327 / 40000000000 : ℚ) +
        (9836124569 / 1000000000000000000 : ℚ) / (2103203999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (108717737 / 62500000000 : ℚ) + (2031207823 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2243636029 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12498]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12498 :
    2 * 160 < 12498 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998049 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12498 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12499 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12499. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12499 : WorldParameters where
  hiddenCharge := (1181037159 / 1000000000000 : ℝ)
  frame := (314227430707 / 500000000000 : ℝ)
  moment := (614629171 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12499 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (742250750889 / 500000000000 : ℝ)
    root := (8636437913 / 1000000000000 : ℝ) }

noncomputable def scalar12499 : ScalarCertificate 12499 world12499 agent12499 where
  dimensionLo := 12499
  dimensionHi := 12499
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2103555799 / 1000000000000 : ℝ)
  frameLo := (314227430707 / 500000000000 : ℝ)
  frameHi := (742250750889 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12499]
  agentFrame_pos := by norm_num only [agent12499]
  worldRadius := (2103555799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12499]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (347596091 / 200000000000 : ℝ)
  lowerTail := (2029576711 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8970154899 / 1000000000000 : ℝ)
  ledger := by
    have h : (1181037159 / 1000000000000 : ℚ) +
        (614629171 / 62500000000000000 : ℚ) / (2103555799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (347596091 / 200000000000 : ℚ) + (2029576711 / 1000000000000 : ℚ) ≤
        (8970154899 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1181037159 / 1000000000000 : ℚ) +
        (614629171 / 62500000000000000 : ℚ) / (2103555799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (347596091 / 200000000000 : ℚ) + (2029576711 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8970154899 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12499]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12499 :
    2 * 160 < 12499 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998011 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12499 {← IO.monoMsNow}" : IO Unit)
