import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12875 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12875. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12875 : WorldParameters where
  hiddenCharge := (1164575497 / 1000000000000 : ℝ)
  frame := (155809411191 / 250000000000 : ℝ)
  moment := (9101037301 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12875 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367310937073 / 250000000000 : ℝ)
    root := (8379195479 / 1000000000000 : ℝ) }

noncomputable def scalar12875 : ScalarCertificate 12875 world12875 agent12875 where
  dimensionLo := 12875
  dimensionHi := 12875
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2241874899 / 1000000000000 : ℝ)
  frameLo := (155809411191 / 250000000000 : ℝ)
  frameHi := (367310937073 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12875]
  agentFrame_pos := by norm_num only [agent12875]
  worldRadius := (2241874899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12875]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1254857537 / 1000000000000 : ℝ)
  lowerTail := (299633671 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (60220301 / 8000000000 : ℝ)
  ledger := by
    have h : (1164575497 / 1000000000000 : ℚ) +
        (9101037301 / 1000000000000000000 : ℚ) / (2241874899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1254857537 / 1000000000000 : ℚ) + (299633671 / 200000000000 : ℚ) ≤
        (60220301 / 8000000000 : ℚ) := by norm_num only
    have hc : (((1164575497 / 1000000000000 : ℚ) +
        (9101037301 / 1000000000000000000 : ℚ) / (2241874899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1254857537 / 1000000000000 : ℚ) + (299633671 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((60220301 / 8000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12875]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12875 :
    2 * 160 < 12875 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999067 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12875 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12876 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12876. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12876 : WorldParameters where
  hiddenCharge := (36391683 / 31250000000 : ℝ)
  frame := (623224182713 / 1000000000000 : ℝ)
  moment := (1819838223 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12876 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1469213360737 / 1000000000000 : ℝ)
    root := (8378548177 / 1000000000000 : ℝ) }

noncomputable def scalar12876 : ScalarCertificate 12876 world12876 agent12876 where
  dimensionLo := 12876
  dimensionHi := 12876
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2242234999 / 1000000000000 : ℝ)
  frameLo := (623224182713 / 1000000000000 : ℝ)
  frameHi := (1469213360737 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12876]
  agentFrame_pos := by norm_num only [agent12876]
  worldRadius := (2242234999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12876]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (626908289 / 500000000000 : ℝ)
  lowerTail := (59880577 / 40000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7524352311 / 1000000000000 : ℝ)
  ledger := by
    have h : (36391683 / 31250000000 : ℚ) +
        (1819838223 / 200000000000000000 : ℚ) / (2242234999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (626908289 / 500000000000 : ℚ) + (59880577 / 40000000000 : ℚ) ≤
        (7524352311 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((36391683 / 31250000000 : ℚ) +
        (1819838223 / 200000000000000000 : ℚ) / (2242234999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (626908289 / 500000000000 : ℚ) + (59880577 / 40000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7524352311 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12876]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12876 :
    2 * 160 < 12876 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (312499933 / 31250000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12876 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12877 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12877. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12877 : WorldParameters where
  hiddenCharge := (582246113 / 500000000000 : ℝ)
  frame := (311605361393 / 500000000000 : ℝ)
  moment := (9097345453 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12877 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (73459139591 / 50000000000 : ℝ)
    root := (1047237633 / 125000000000 : ℝ) }

noncomputable def scalar12877 : ScalarCertificate 12877 world12877 agent12877 where
  dimensionLo := 12877
  dimensionHi := 12877
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2242595399 / 1000000000000 : ℝ)
  frameLo := (311605361393 / 500000000000 : ℝ)
  frameHi := (73459139591 / 50000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12877]
  agentFrame_pos := by norm_num only [agent12877]
  worldRadius := (2242595399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12877]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (626388037 / 500000000000 : ℝ)
  lowerTail := (1495860827 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1880291983 / 250000000000 : ℝ)
  ledger := by
    have h : (582246113 / 500000000000 : ℚ) +
        (9097345453 / 1000000000000000000 : ℚ) / (2242595399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (626388037 / 500000000000 : ℚ) + (1495860827 / 1000000000000 : ℚ) ≤
        (1880291983 / 250000000000 : ℚ) := by norm_num only
    have hc : (((582246113 / 500000000000 : ℚ) +
        (9097345453 / 1000000000000000000 : ℚ) / (2242595399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (626388037 / 500000000000 : ℚ) + (1495860827 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1880291983 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12877]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12877 :
    2 * 160 < 12877 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995377 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12877 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12878 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12878. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12878 : WorldParameters where
  hiddenCharge := (1164450607 / 1000000000000 : ℝ)
  frame := (311598632491 / 500000000000 : ℝ)
  moment := (4547750157 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12878 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1469152235723 / 1000000000000 : ℝ)
    root := (8377254141 / 1000000000000 : ℝ) }

noncomputable def scalar12878 : ScalarCertificate 12878 world12878 agent12878 where
  dimensionLo := 12878
  dimensionHi := 12878
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2242955899 / 1000000000000 : ℝ)
  frameLo := (311598632491 / 500000000000 : ℝ)
  frameHi := (1469152235723 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12878]
  agentFrame_pos := by norm_num only [agent12878]
  worldRadius := (2242955899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12878]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (156467079 / 125000000000 : ℝ)
  lowerTail := (1494708343 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7517986199 / 1000000000000 : ℝ)
  ledger := by
    have h : (1164450607 / 1000000000000 : ℚ) +
        (4547750157 / 500000000000000000 : ℚ) / (2242955899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (156467079 / 125000000000 : ℚ) + (1494708343 / 1000000000000 : ℚ) ≤
        (7517986199 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1164450607 / 1000000000000 : ℚ) +
        (4547750157 / 500000000000000000 : ℚ) / (2242955899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (156467079 / 125000000000 : ℚ) + (1494708343 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7517986199 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12878]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12878 :
    2 * 160 < 12878 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996269 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12878 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12879 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12879. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12879 : WorldParameters where
  hiddenCharge := (582204499 / 500000000000 : ℝ)
  frame := (623183809301 / 1000000000000 : ℝ)
  moment := (4546827849 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12879 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367280424581 / 250000000000 : ℝ)
    root := (4188303671 / 500000000000 : ℝ) }

noncomputable def scalar12879 : ScalarCertificate 12879 world12879 agent12879 where
  dimensionLo := 12879
  dimensionHi := 12879
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2243316299 / 1000000000000 : ℝ)
  frameLo := (623183809301 / 1000000000000 : ℝ)
  frameHi := (367280424581 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12879]
  agentFrame_pos := by norm_num only [agent12879]
  worldRadius := (2243316299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12879]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (625349037 / 500000000000 : ℝ)
  lowerTail := (1493556781 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (939350883 / 125000000000 : ℝ)
  ledger := by
    have h : (582204499 / 500000000000 : ℚ) +
        (4546827849 / 500000000000000000 : ℚ) / (2243316299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (625349037 / 500000000000 : ℚ) + (1493556781 / 1000000000000 : ℚ) ≤
        (939350883 / 125000000000 : ℚ) := by norm_num only
    have hc : (((582204499 / 500000000000 : ℚ) +
        (4546827849 / 500000000000000000 : ℚ) / (2243316299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (625349037 / 500000000000 : ℚ) + (1493556781 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((939350883 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12879]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12879 :
    2 * 160 < 12879 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997463 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12879 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12880 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12880. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12880 : WorldParameters where
  hiddenCharge := (1164367401 / 1000000000000 : ℝ)
  frame := (623170355743 / 1000000000000 : ℝ)
  moment := (2272952901 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12880 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (293802371103 / 200000000000 : ℝ)
    root := (4187980399 / 500000000000 : ℝ) }

noncomputable def scalar12880 : ScalarCertificate 12880 world12880 agent12880 where
  dimensionLo := 12880
  dimensionHi := 12880
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2243791499 / 1000000000000 : ℝ)
  frameLo := (623170355743 / 1000000000000 : ℝ)
  frameHi := (293802371103 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12880]
  agentFrame_pos := by norm_num only [agent12880]
  worldRadius := (2243791499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12880]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1249437723 / 1000000000000 : ℝ)
  lowerTail := (373029021 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7510932829 / 1000000000000 : ℝ)
  ledger := by
    have h : (1164367401 / 1000000000000 : ℚ) +
        (2272952901 / 250000000000000000 : ℚ) / (2243791499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1249437723 / 1000000000000 : ℚ) + (373029021 / 250000000000 : ℚ) ≤
        (7510932829 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1164367401 / 1000000000000 : ℚ) +
        (2272952901 / 250000000000000000 : ℚ) / (2243791499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1249437723 / 1000000000000 : ℚ) + (373029021 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7510932829 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12880]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12880 :
    2 * 160 < 12880 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996911 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12880 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12881 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12881. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12881 : WorldParameters where
  hiddenCharge := (582162907 / 500000000000 : ℝ)
  frame := (623156904307 / 1000000000000 : ℝ)
  moment := (9089968033 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12881 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1468981350519 / 1000000000000 : ℝ)
    root := (8375314443 / 1000000000000 : ℝ) }

noncomputable def scalar12881 : ScalarCertificate 12881 world12881 agent12881 where
  dimensionLo := 12881
  dimensionHi := 12881
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2244151999 / 1000000000000 : ℝ)
  frameLo := (623156904307 / 1000000000000 : ℝ)
  frameHi := (1468981350519 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12881]
  agentFrame_pos := by norm_num only [agent12881]
  worldRadius := (2244151999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12881]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (624200717 / 500000000000 : ℝ)
  lowerTail := (745483461 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3753879793 / 500000000000 : ℝ)
  ledger := by
    have h : (582162907 / 500000000000 : ℚ) +
        (9089968033 / 1000000000000000000 : ℚ) / (2244151999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (624200717 / 500000000000 : ℚ) + (745483461 / 500000000000 : ℚ) ≤
        (3753879793 / 500000000000 : ℚ) := by norm_num only
    have hc : (((582162907 / 500000000000 : ℚ) +
        (9089968033 / 1000000000000000000 : ℚ) / (2244151999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (624200717 / 500000000000 : ℚ) + (745483461 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3753879793 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12881]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12881 :
    2 * 160 < 12881 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998307 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12881 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12882 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12882. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12882 : WorldParameters where
  hiddenCharge := (582142119 / 500000000000 : ℝ)
  frame := (38946465937 / 62500000000 : ℝ)
  moment := (1136015623 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12882 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1468950858313 / 1000000000000 : ℝ)
    root := (8374668277 / 1000000000000 : ℝ) }

noncomputable def scalar12882 : ScalarCertificate 12882 world12882 agent12882 where
  dimensionLo := 12882
  dimensionHi := 12882
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2244512499 / 1000000000000 : ℝ)
  frameLo := (38946465937 / 62500000000 : ℝ)
  frameHi := (1468950858313 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12882]
  agentFrame_pos := by norm_num only [agent12882]
  worldRadius := (2244512499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12882]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1247366127 / 1000000000000 : ℝ)
  lowerTail := (1489818783 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7504588979 / 1000000000000 : ℝ)
  ledger := by
    have h : (582142119 / 500000000000 : ℚ) +
        (1136015623 / 125000000000000000 : ℚ) / (2244512499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1247366127 / 1000000000000 : ℚ) + (1489818783 / 1000000000000 : ℚ) ≤
        (7504588979 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((582142119 / 500000000000 : ℚ) +
        (1136015623 / 125000000000000000 : ℚ) / (2244512499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1247366127 / 1000000000000 : ℚ) + (1489818783 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7504588979 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12882]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12882 :
    2 * 160 < 12882 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999921 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12882 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12883 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12883. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12883 : WorldParameters where
  hiddenCharge := (1164242673 / 1000000000000 : ℝ)
  frame := (311565003899 / 500000000000 : ℝ)
  moment := (4543141229 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12883 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (734460195327 / 500000000000 : ℝ)
    root := (2093505559 / 250000000000 : ℝ) }

noncomputable def scalar12883 : ScalarCertificate 12883 world12883 agent12883 where
  dimensionLo := 12883
  dimensionHi := 12883
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2244872999 / 1000000000000 : ℝ)
  frameLo := (311565003899 / 500000000000 : ℝ)
  frameHi := (734460195327 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12883]
  agentFrame_pos := by norm_num only [agent12883]
  worldRadius := (2244872999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12883]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (623165899 / 500000000000 : ℝ)
  lowerTail := (372167919 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7501421011 / 1000000000000 : ℝ)
  ledger := by
    have h : (1164242673 / 1000000000000 : ℚ) +
        (4543141229 / 500000000000000000 : ℚ) / (2244872999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (623165899 / 500000000000 : ℚ) + (372167919 / 250000000000 : ℚ) ≤
        (7501421011 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1164242673 / 1000000000000 : ℚ) +
        (4543141229 / 500000000000000000 : ℚ) / (2244872999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (623165899 / 500000000000 : ℚ) + (372167919 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7501421011 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12883]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12883 :
    2 * 160 < 12883 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997337 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12883 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12884 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12884. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12884 : WorldParameters where
  hiddenCharge := (1164201119 / 1000000000000 : ℝ)
  frame := (24924662509 / 40000000000 : ℝ)
  moment := (9084440453 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12884 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1468889929887 / 1000000000000 : ℝ)
    root := (130834007 / 15625000000 : ℝ) }

noncomputable def scalar12884 : ScalarCertificate 12884 world12884 agent12884 where
  dimensionLo := 12884
  dimensionHi := 12884
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2245233499 / 1000000000000 : ℝ)
  frameLo := (24924662509 / 40000000000 : ℝ)
  frameHi := (1468889929887 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12884]
  agentFrame_pos := by norm_num only [agent12884]
  worldRadius := (2245233499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12884]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (622649237 / 500000000000 : ℝ)
  lowerTail := (1487525611 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3749127859 / 500000000000 : ℝ)
  ledger := by
    have h : (1164201119 / 1000000000000 : ℚ) +
        (9084440453 / 1000000000000000000 : ℚ) / (2245233499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (622649237 / 500000000000 : ℚ) + (1487525611 / 1000000000000 : ℚ) ≤
        (3749127859 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1164201119 / 1000000000000 : ℚ) +
        (9084440453 / 1000000000000000000 : ℚ) / (2245233499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (622649237 / 500000000000 : ℚ) + (1487525611 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3749127859 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12884]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12884 :
    2 * 160 < 12884 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998581 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12884 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12885 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12885. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12885 : WorldParameters where
  hiddenCharge := (145519947 / 125000000000 : ℝ)
  frame := (623103119771 / 1000000000000 : ℝ)
  moment := (908259897 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12885 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1468859493651 / 1000000000000 : ℝ)
    root := (8372730849 / 1000000000000 : ℝ) }

noncomputable def scalar12885 : ScalarCertificate 12885 world12885 agent12885 where
  dimensionLo := 12885
  dimensionHi := 12885
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2245593999 / 1000000000000 : ℝ)
  frameLo := (623103119771 / 1000000000000 : ℝ)
  frameHi := (1468859493651 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12885]
  agentFrame_pos := by norm_num only [agent12885]
  worldRadius := (2245593999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12885]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (622133087 / 500000000000 : ℝ)
  lowerTail := (2378209 / 1600000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1873773289 / 250000000000 : ℝ)
  ledger := by
    have h : (145519947 / 125000000000 : ℚ) +
        (908259897 / 100000000000000000 : ℚ) / (2245593999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (622133087 / 500000000000 : ℚ) + (2378209 / 1600000000 : ℚ) ≤
        (1873773289 / 250000000000 : ℚ) := by norm_num only
    have hc : (((145519947 / 125000000000 : ℚ) +
        (908259897 / 100000000000000000 : ℚ) / (2245593999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (622133087 / 500000000000 : ℚ) + (2378209 / 1600000000 : ℚ) : ℚ) : ℝ) ≤
        ((1873773289 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12885]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12885 :
    2 * 160 < 12885 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997259 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12885 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12886 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12886. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12886 : WorldParameters where
  hiddenCharge := (291029511 / 250000000000 : ℝ)
  frame := (623089678937 / 1000000000000 : ℝ)
  moment := (9080758009 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12886 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1468829064291 / 1000000000000 : ℝ)
    root := (8372085439 / 1000000000000 : ℝ) }

noncomputable def scalar12886 : ScalarCertificate 12886 world12886 agent12886 where
  dimensionLo := 12886
  dimensionHi := 12886
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2245954499 / 1000000000000 : ℝ)
  frameLo := (623089678937 / 1000000000000 : ℝ)
  frameHi := (1468829064291 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12886]
  agentFrame_pos := by norm_num only [agent12886]
  worldRadius := (2245954499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12886]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (124323483 / 100000000000 : ℝ)
  lowerTail := (148523663 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7491933167 / 1000000000000 : ℝ)
  ledger := by
    have h : (291029511 / 250000000000 : ℚ) +
        (9080758009 / 1000000000000000000 : ℚ) / (2245954499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (124323483 / 100000000000 : ℚ) + (148523663 / 100000000000 : ℚ) ≤
        (7491933167 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((291029511 / 250000000000 : ℚ) +
        (9080758009 / 1000000000000000000 : ℚ) / (2245954499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (124323483 / 100000000000 : ℚ) + (148523663 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7491933167 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12886]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12886 :
    2 * 160 < 12886 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999907 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12886 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12887 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12887. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12887 : WorldParameters where
  hiddenCharge := (582038261 / 500000000000 : ℝ)
  frame := (623076240221 / 1000000000000 : ℝ)
  moment := (9078917569 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12887 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1468798659447 / 1000000000000 : ℝ)
    root := (8371440153 / 1000000000000 : ℝ) }

noncomputable def scalar12887 : ScalarCertificate 12887 world12887 agent12887 where
  dimensionLo := 12887
  dimensionHi := 12887
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2246314999 / 1000000000000 : ℝ)
  frameLo := (623076240221 / 1000000000000 : ℝ)
  frameHi := (1468798659447 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12887]
  agentFrame_pos := by norm_num only [agent12887]
  worldRadius := (2246314999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12887]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1242204459 / 1000000000000 : ℝ)
  lowerTail := (1484093661 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1497755161 / 200000000000 : ℝ)
  ledger := by
    have h : (582038261 / 500000000000 : ℚ) +
        (9078917569 / 1000000000000000000 : ℚ) / (2246314999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1242204459 / 1000000000000 : ℚ) + (1484093661 / 1000000000000 : ℚ) ≤
        (1497755161 / 200000000000 : ℚ) := by norm_num only
    have hc : (((582038261 / 500000000000 : ℚ) +
        (9078917569 / 1000000000000000000 : ℚ) / (2246314999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1242204459 / 1000000000000 : ℚ) + (1484093661 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1497755161 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12887]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12887 :
    2 * 160 < 12887 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (399999839 / 40000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12887 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12888 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12888. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12888 : WorldParameters where
  hiddenCharge := (1164035011 / 1000000000000 : ℝ)
  frame := (623062803623 / 1000000000000 : ℝ)
  moment := (9077077651 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12888 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (734384133673 / 500000000000 : ℝ)
    root := (8370795119 / 1000000000000 : ℝ) }

noncomputable def scalar12888 : ScalarCertificate 12888 world12888 agent12888 where
  dimensionLo := 12888
  dimensionHi := 12888
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2246675599 / 1000000000000 : ℝ)
  frameLo := (623062803623 / 1000000000000 : ℝ)
  frameHi := (734384133673 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12888]
  agentFrame_pos := by norm_num only [agent12888]
  worldRadius := (2246675599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12888]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (310293797 / 250000000000 : ℝ)
  lowerTail := (370737961 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (187140529 / 25000000000 : ℝ)
  ledger := by
    have h : (1164035011 / 1000000000000 : ℚ) +
        (9077077651 / 1000000000000000000 : ℚ) / (2246675599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (310293797 / 250000000000 : ℚ) + (370737961 / 250000000000 : ℚ) ≤
        (187140529 / 25000000000 : ℚ) := by norm_num only
    have hc : (((1164035011 / 1000000000000 : ℚ) +
        (9077077651 / 1000000000000000000 : ℚ) / (2246675599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (310293797 / 250000000000 : ℚ) + (370737961 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((187140529 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12888]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12888 :
    2 * 160 < 12888 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995853 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12888 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12889 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12889. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12889 : WorldParameters where
  hiddenCharge := (1163993511 / 1000000000000 : ℝ)
  frame := (77881171143 / 125000000000 : ℝ)
  moment := (9075238253 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12889 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1468737887981 / 1000000000000 : ℝ)
    root := (334806011 / 40000000000 : ℝ) }

noncomputable def scalar12889 : ScalarCertificate 12889 world12889 agent12889 where
  dimensionLo := 12889
  dimensionHi := 12889
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2247035999 / 1000000000000 : ℝ)
  frameLo := (77881171143 / 125000000000 : ℝ)
  frameHi := (1468737887981 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12889]
  agentFrame_pos := by norm_num only [agent12889]
  worldRadius := (2247035999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12889]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1240146739 / 1000000000000 : ℝ)
  lowerTail := (740905437 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3741234567 / 500000000000 : ℝ)
  ledger := by
    have h : (1163993511 / 1000000000000 : ℚ) +
        (9075238253 / 1000000000000000000 : ℚ) / (2247035999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1240146739 / 1000000000000 : ℚ) + (740905437 / 500000000000 : ℚ) ≤
        (3741234567 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1163993511 / 1000000000000 : ℚ) +
        (9075238253 / 1000000000000000000 : ℚ) / (2247035999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1240146739 / 1000000000000 : ℚ) + (740905437 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3741234567 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12889]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12889 :
    2 * 160 < 12889 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999859 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12889 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12890 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12890. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12890 : WorldParameters where
  hiddenCharge := (581976011 / 500000000000 : ℝ)
  frame := (623035936781 / 1000000000000 : ℝ)
  moment := (567087461 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12890 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1468628321887 / 1000000000000 : ℝ)
    root := (8369505553 / 1000000000000 : ℝ) }

noncomputable def scalar12890 : ScalarCertificate 12890 world12890 agent12890 where
  dimensionLo := 12890
  dimensionHi := 12890
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2247511499 / 1000000000000 : ℝ)
  frameLo := (623035936781 / 1000000000000 : ℝ)
  frameHi := (1468628321887 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12890]
  agentFrame_pos := by norm_num only [agent12890]
  worldRadius := (2247511499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12890]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1238898593 / 1000000000000 : ℝ)
  lowerTail := (1480383317 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (149572549 / 20000000000 : ℝ)
  ledger := by
    have h : (581976011 / 500000000000 : ℚ) +
        (567087461 / 62500000000000000 : ℚ) / (2247511499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1238898593 / 1000000000000 : ℚ) + (1480383317 / 1000000000000 : ℚ) ≤
        (149572549 / 20000000000 : ℚ) := by norm_num only
    have hc : (((581976011 / 500000000000 : ℚ) +
        (567087461 / 62500000000000000 : ℚ) / (2247511499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1238898593 / 1000000000000 : ℚ) + (1480383317 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((149572549 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12890]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12890 :
    2 * 160 < 12890 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999881 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12890 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12891 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12891. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12891 : WorldParameters where
  hiddenCharge := (72744409 / 62500000000 : ℝ)
  frame := (124604501307 / 200000000000 : ℝ)
  moment := (453578051 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12891 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1468597980643 / 1000000000000 : ℝ)
    root := (1673772217 / 200000000000 : ℝ) }

noncomputable def scalar12891 : ScalarCertificate 12891 world12891 agent12891 where
  dimensionLo := 12891
  dimensionHi := 12891
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2247871999 / 1000000000000 : ℝ)
  frameLo := (124604501307 / 200000000000 : ℝ)
  frameHi := (1468597980643 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12891]
  agentFrame_pos := by norm_num only [agent12891]
  worldRadius := (2247871999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12891]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1237872363 / 1000000000000 : ℝ)
  lowerTail := (739622351 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7475481211 / 1000000000000 : ℝ)
  ledger := by
    have h : (72744409 / 62500000000 : ℚ) +
        (453578051 / 50000000000000000 : ℚ) / (2247871999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1237872363 / 1000000000000 : ℚ) + (739622351 / 500000000000 : ℚ) ≤
        (7475481211 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((72744409 / 62500000000 : ℚ) +
        (453578051 / 50000000000000000 : ℚ) / (2247871999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1237872363 / 1000000000000 : ℚ) + (739622351 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7475481211 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12891]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12891 :
    2 * 160 < 12891 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997429 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12891 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12892 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12892. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12892 : WorldParameters where
  hiddenCharge := (290967269 / 250000000000 : ℝ)
  frame := (124601815681 / 200000000000 : ℝ)
  moment := (566857699 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12892 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (91785478257 / 62500000000 : ℝ)
    root := (2092054201 / 250000000000 : ℝ) }

noncomputable def scalar12892 : ScalarCertificate 12892 world12892 agent12892 where
  dimensionLo := 12892
  dimensionHi := 12892
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2248232599 / 1000000000000 : ℝ)
  frameLo := (124601815681 / 200000000000 : ℝ)
  frameHi := (91785478257 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12892]
  agentFrame_pos := by norm_num only [agent12892]
  worldRadius := (2248232599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12892]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (61842359 / 50000000000 : ℝ)
  lowerTail := (92381699 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7472337579 / 1000000000000 : ℝ)
  ledger := by
    have h : (290967269 / 250000000000 : ℚ) +
        (566857699 / 62500000000000000 : ℚ) / (2248232599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (61842359 / 50000000000 : ℚ) + (92381699 / 62500000000 : ℚ) ≤
        (7472337579 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((290967269 / 250000000000 : ℚ) +
        (566857699 / 62500000000000000 : ℚ) / (2248232599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (61842359 / 50000000000 : ℚ) + (92381699 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((7472337579 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12892]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12892 :
    2 * 160 < 12892 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999853 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12892 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12893 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12893. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12893 : WorldParameters where
  hiddenCharge := (58191381 / 50000000000 : ℝ)
  frame := (622995652391 / 1000000000000 : ℝ)
  moment := (9067885869 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12893 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (734268671083 / 500000000000 : ℝ)
    root := (1045946589 / 125000000000 : ℝ) }

noncomputable def scalar12893 : ScalarCertificate 12893 world12893 agent12893 where
  dimensionLo := 12893
  dimensionHi := 12893
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2248593099 / 1000000000000 : ℝ)
  frameLo := (622995652391 / 1000000000000 : ℝ)
  frameHi := (734268671083 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12893]
  agentFrame_pos := by norm_num only [agent12893]
  worldRadius := (2248593099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12893]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1235822913 / 1000000000000 : ℝ)
  lowerTail := (1476970623 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1493839321 / 200000000000 : ℝ)
  ledger := by
    have h : (58191381 / 50000000000 : ℚ) +
        (9067885869 / 1000000000000000000 : ℚ) / (2248593099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1235822913 / 1000000000000 : ℚ) + (1476970623 / 1000000000000 : ℚ) ≤
        (1493839321 / 200000000000 : ℚ) := by norm_num only
    have hc : (((58191381 / 50000000000 : ℚ) +
        (9067885869 / 1000000000000000000 : ℚ) / (2248593099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1235822913 / 1000000000000 : ℚ) + (1476970623 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1493839321 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12893]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12893 :
    2 * 160 < 12893 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997077 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12893 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12894 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12894. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12894 : WorldParameters where
  hiddenCharge := (581893087 / 500000000000 : ℝ)
  frame := (155745557123 / 250000000000 : ℝ)
  moment := (4533024537 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12894 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (734253522459 / 500000000000 : ℝ)
    root := (4183464371 / 500000000000 : ℝ) }

noncomputable def scalar12894 : ScalarCertificate 12894 world12894 agent12894 where
  dimensionLo := 12894
  dimensionHi := 12894
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2248953699 / 1000000000000 : ℝ)
  frameLo := (155745557123 / 250000000000 : ℝ)
  frameHi := (734253522459 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12894]
  agentFrame_pos := by norm_num only [agent12894]
  worldRadius := (2248953699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12894]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1234799643 / 1000000000000 : ℝ)
  lowerTail := (1475835107 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (933257267 / 125000000000 : ℝ)
  ledger := by
    have h : (581893087 / 500000000000 : ℚ) +
        (4533024537 / 500000000000000000 : ℚ) / (2248953699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1234799643 / 1000000000000 : ℚ) + (1475835107 / 1000000000000 : ℚ) ≤
        (933257267 / 125000000000 : ℚ) := by norm_num only
    have hc : (((581893087 / 500000000000 : ℚ) +
        (4533024537 / 500000000000000000 : ℚ) / (2248953699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1234799643 / 1000000000000 : ℚ) + (1475835107 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((933257267 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12894]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12894 :
    2 * 160 < 12894 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999331 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12894 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12895 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12895. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12895 : WorldParameters where
  hiddenCharge := (1163744739 / 1000000000000 : ℝ)
  frame := (622968806707 / 1000000000000 : ℝ)
  moment := (4532106399 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12895 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1468476766239 / 1000000000000 : ℝ)
    root := (334651401 / 40000000000 : ℝ) }

noncomputable def scalar12895 : ScalarCertificate 12895 world12895 agent12895 where
  dimensionLo := 12895
  dimensionHi := 12895
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2249314299 / 1000000000000 : ℝ)
  frameLo := (622968806707 / 1000000000000 : ℝ)
  frameHi := (1468476766239 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12895]
  agentFrame_pos := by norm_num only [agent12895]
  worldRadius := (2249314299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12895]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (308444353 / 250000000000 : ℝ)
  lowerTail := (1474700679 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3731461209 / 500000000000 : ℝ)
  ledger := by
    have h : (1163744739 / 1000000000000 : ℚ) +
        (4532106399 / 500000000000000000 : ℚ) / (2249314299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (308444353 / 250000000000 : ℚ) + (1474700679 / 1000000000000 : ℚ) ≤
        (3731461209 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1163744739 / 1000000000000 : ℚ) +
        (4532106399 / 500000000000000000 : ℚ) / (2249314299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (308444353 / 250000000000 : ℚ) + (1474700679 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3731461209 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12895]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12895 :
    2 * 160 < 12895 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997649 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12895 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12896 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12896. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12896 : WorldParameters where
  hiddenCharge := (581851657 / 500000000000 : ℝ)
  frame := (155738846759 / 250000000000 : ℝ)
  moment := (4531188521 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12896 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (734223250121 / 500000000000 : ℝ)
    root := (1673128299 / 200000000000 : ℝ) }

noncomputable def scalar12896 : ScalarCertificate 12896 world12896 agent12896 where
  dimensionLo := 12896
  dimensionHi := 12896
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2249674799 / 1000000000000 : ℝ)
  frameLo := (155738846759 / 250000000000 : ℝ)
  frameHi := (734223250121 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12896]
  agentFrame_pos := by norm_num only [agent12896]
  worldRadius := (2249674799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12896]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1232756071 / 1000000000000 : ℝ)
  lowerTail := (184195897 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7459789297 / 1000000000000 : ℝ)
  ledger := by
    have h : (581851657 / 500000000000 : ℚ) +
        (4531188521 / 500000000000000000 : ℚ) / (2249674799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1232756071 / 1000000000000 : ℚ) + (184195897 / 125000000000 : ℚ) ≤
        (7459789297 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((581851657 / 500000000000 : ℚ) +
        (4531188521 / 500000000000000000 : ℚ) / (2249674799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1232756071 / 1000000000000 : ℚ) + (184195897 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7459789297 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12896]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12896 :
    2 * 160 < 12896 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (624999977 / 62500000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12896 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12897 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12897. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12897 : WorldParameters where
  hiddenCharge := (1163661901 / 1000000000000 : ℝ)
  frame := (622941969479 / 1000000000000 : ℝ)
  moment := (4530270903 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12897 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (458880079 / 312500000 : ℝ)
    root := (1045624761 / 125000000000 : ℝ) }

noncomputable def scalar12897 : ScalarCertificate 12897 world12897 agent12897 where
  dimensionLo := 12897
  dimensionHi := 12897
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2250035499 / 1000000000000 : ℝ)
  frameLo := (622941969479 / 1000000000000 : ℝ)
  frameHi := (458880079 / 312500000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12897]
  agentFrame_pos := by norm_num only [agent12897]
  worldRadius := (2250035499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12897]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (615867911 / 500000000000 : ℝ)
  lowerTail := (368108707 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (298266349 / 40000000000 : ℝ)
  ledger := by
    have h : (1163661901 / 1000000000000 : ℚ) +
        (4530270903 / 500000000000000000 : ℚ) / (2250035499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (615867911 / 500000000000 : ℚ) + (368108707 / 250000000000 : ℚ) ≤
        (298266349 / 40000000000 : ℚ) := by norm_num only
    have hc : (((1163661901 / 1000000000000 : ℚ) +
        (4530270903 / 500000000000000000 : ℚ) / (2250035499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (615867911 / 500000000000 : ℚ) + (368108707 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((298266349 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12897]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12897 :
    2 * 160 < 12897 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998973 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12897 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12898 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12898. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12898 : WorldParameters where
  hiddenCharge := (581810249 / 500000000000 : ℝ)
  frame := (311464277017 / 500000000000 : ℝ)
  moment := (9058707089 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12898 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (45887063247 / 31250000000 : ℝ)
    root := (8364354933 / 1000000000000 : ℝ) }

noncomputable def scalar12898 : ScalarCertificate 12898 world12898 agent12898 where
  dimensionLo := 12898
  dimensionHi := 12898
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2250396099 / 1000000000000 : ℝ)
  frameLo := (311464277017 / 500000000000 : ℝ)
  frameHi := (45887063247 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12898]
  agentFrame_pos := by norm_num only [agent12898]
  worldRadius := (2250396099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12898]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1230716533 / 1000000000000 : ℝ)
  lowerTail := (36782587 / 25000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3726765447 / 500000000000 : ℝ)
  ledger := by
    have h : (581810249 / 500000000000 : ℚ) +
        (9058707089 / 1000000000000000000 : ℚ) / (2250396099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1230716533 / 1000000000000 : ℚ) + (36782587 / 25000000000 : ℚ) ≤
        (3726765447 / 500000000000 : ℚ) := by norm_num only
    have hc : (((581810249 / 500000000000 : ℚ) +
        (9058707089 / 1000000000000000000 : ℚ) / (2250396099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1230716533 / 1000000000000 : ℚ) + (36782587 / 25000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3726765447 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12898]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12898 :
    2 * 160 < 12898 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995649 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12898 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12899 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12899. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12899 : WorldParameters where
  hiddenCharge := (581789553 / 500000000000 : ℝ)
  frame := (311457570351 / 500000000000 : ℝ)
  moment := (9056872891 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12899 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1468355807667 / 1000000000000 : ℝ)
    root := (1672742393 / 200000000000 : ℝ) }

noncomputable def scalar12899 : ScalarCertificate 12899 world12899 agent12899 where
  dimensionLo := 12899
  dimensionHi := 12899
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2250756699 / 1000000000000 : ℝ)
  frameLo := (311457570351 / 500000000000 : ℝ)
  frameHi := (1468355807667 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12899]
  agentFrame_pos := by norm_num only [agent12899]
  worldRadius := (2250756699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12899]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1229698207 / 1000000000000 : ℝ)
  lowerTail := (735086569 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7450405653 / 1000000000000 : ℝ)
  ledger := by
    have h : (581789553 / 500000000000 : ℚ) +
        (9056872891 / 1000000000000000000 : ℚ) / (2250756699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1229698207 / 1000000000000 : ℚ) + (735086569 / 500000000000 : ℚ) ≤
        (7450405653 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((581789553 / 500000000000 : ℚ) +
        (9056872891 / 1000000000000000000 : ℚ) / (2250756699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1229698207 / 1000000000000 : ℚ) + (735086569 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7450405653 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12899]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12899 :
    2 * 160 < 12899 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995259 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12899 {← IO.monoMsNow}" : IO Unit)
