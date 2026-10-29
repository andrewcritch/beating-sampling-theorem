import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 13000 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13000. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13000 : WorldParameters where
  hiddenCharge := (115945343 / 100000000000 : ℝ)
  frame := (155392795483 / 250000000000 : ℝ)
  moment := (4437129981 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13000 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (366121917123 / 250000000000 : ℝ)
    root := (1037463949 / 125000000000 : ℝ) }

noncomputable def scalar13000 : ScalarCertificate 13000 world13000 agent13000 where
  dimensionLo := 13000
  dimensionHi := 13000
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2288540499 / 1000000000000 : ℝ)
  frameLo := (155392795483 / 250000000000 : ℝ)
  frameHi := (366121917123 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13000]
  agentFrame_pos := by norm_num only [agent13000]
  worldRadius := (2288540499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13000]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1129408659 / 1000000000000 : ℝ)
  lowerTail := (339522223 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (446280817 / 62500000000 : ℝ)
  ledger := by
    have h : (115945343 / 100000000000 : ℚ) +
        (4437129981 / 500000000000000000 : ℚ) / (2288540499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1129408659 / 1000000000000 : ℚ) + (339522223 / 250000000000 : ℚ) ≤
        (446280817 / 62500000000 : ℚ) := by norm_num only
    have hc : (((115945343 / 100000000000 : ℚ) +
        (4437129981 / 500000000000000000 : ℚ) / (2288540499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1129408659 / 1000000000000 : ℚ) + (339522223 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((446280817 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13000]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13000 :
    2 * 160 < 13000 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999859 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13000 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13001 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13001. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13001 : WorldParameters where
  hiddenCharge := (1811583 / 1562500000 : ℝ)
  frame := (310778990653 / 500000000000 : ℝ)
  moment := (8872477739 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13001 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1464458382603 / 1000000000000 : ℝ)
    root := (8299087057 / 1000000000000 : ℝ) }

noncomputable def scalar13001 : ScalarCertificate 13001 world13001 agent13001 where
  dimensionLo := 13001
  dimensionHi := 13001
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2288902799 / 1000000000000 : ℝ)
  frameLo := (310778990653 / 500000000000 : ℝ)
  frameHi := (1464458382603 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13001]
  agentFrame_pos := by norm_num only [agent13001]
  worldRadius := (2288902799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13001]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (45139391 / 40000000000 : ℝ)
  lowerTail := (678528751 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3568810477 / 500000000000 : ℝ)
  ledger := by
    have h : (1811583 / 1562500000 : ℚ) +
        (8872477739 / 1000000000000000000 : ℚ) / (2288902799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (45139391 / 40000000000 : ℚ) + (678528751 / 500000000000 : ℚ) ≤
        (3568810477 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1811583 / 1562500000 : ℚ) +
        (8872477739 / 1000000000000000000 : ℚ) / (2288902799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (45139391 / 40000000000 : ℚ) + (678528751 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3568810477 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13001]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13001 :
    2 * 160 < 13001 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998153 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13001 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13002 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13002. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13002 : WorldParameters where
  hiddenCharge := (1159372819 / 1000000000000 : ℝ)
  frame := (310772391369 / 500000000000 : ℝ)
  moment := (8870696017 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13002 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1464429108677 / 1000000000000 : ℝ)
    root := (4149231349 / 500000000000 : ℝ) }

noncomputable def scalar13002 : ScalarCertificate 13002 world13002 agent13002 where
  dimensionLo := 13002
  dimensionHi := 13002
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2289265299 / 1000000000000 : ℝ)
  frameLo := (310772391369 / 500000000000 : ℝ)
  frameHi := (1464429108677 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13002]
  agentFrame_pos := by norm_num only [agent13002]
  worldRadius := (2289265299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13002]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (281890473 / 250000000000 : ℝ)
  lowerTail := (339006793 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3567375589 / 500000000000 : ℝ)
  ledger := by
    have h : (1159372819 / 1000000000000 : ℚ) +
        (8870696017 / 1000000000000000000 : ℚ) / (2289265299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (281890473 / 250000000000 : ℚ) + (339006793 / 250000000000 : ℚ) ≤
        (3567375589 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1159372819 / 1000000000000 : ℚ) +
        (8870696017 / 1000000000000000000 : ℚ) / (2289265299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (281890473 / 250000000000 : ℚ) + (339006793 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3567375589 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13002]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13002 :
    2 * 160 < 13002 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999177 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13002 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13003 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13003. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13003 : WorldParameters where
  hiddenCharge := (1159332529 / 1000000000000 : ℝ)
  frame := (621531586229 / 1000000000000 : ℝ)
  moment := (4434457397 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13003 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1464399846709 / 1000000000000 : ℝ)
    root := (1659567703 / 200000000000 : ℝ) }

noncomputable def scalar13003 : ScalarCertificate 13003 world13003 agent13003 where
  dimensionLo := 13003
  dimensionHi := 13003
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2289627699 / 1000000000000 : ℝ)
  frameLo := (621531586229 / 1000000000000 : ℝ)
  frameHi := (1464399846709 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13003]
  agentFrame_pos := by norm_num only [agent13003]
  worldRadius := (2289627699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13003]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1126639799 / 1000000000000 : ℝ)
  lowerTail := (1354997667 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7131883739 / 1000000000000 : ℝ)
  ledger := by
    have h : (1159332529 / 1000000000000 : ℚ) +
        (4434457397 / 500000000000000000 : ℚ) / (2289627699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1126639799 / 1000000000000 : ℚ) + (1354997667 / 1000000000000 : ℚ) ≤
        (7131883739 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1159332529 / 1000000000000 : ℚ) +
        (4434457397 / 500000000000000000 : ℚ) / (2289627699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1126639799 / 1000000000000 : ℚ) + (1354997667 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7131883739 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13003]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13003 :
    2 * 160 < 13003 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999889 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13003 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13004 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13004. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13004 : WorldParameters where
  hiddenCharge := (1159292249 / 1000000000000 : ℝ)
  frame := (621518391777 / 1000000000000 : ℝ)
  moment := (1108391759 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13004 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (366092650637 / 250000000000 : ℝ)
    root := (8297214507 / 1000000000000 : ℝ) }

noncomputable def scalar13004 : ScalarCertificate 13004 world13004 agent13004 where
  dimensionLo := 13004
  dimensionHi := 13004
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2289990299 / 1000000000000 : ℝ)
  frameLo := (621518391777 / 1000000000000 : ℝ)
  frameHi := (366092650637 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13004]
  agentFrame_pos := by norm_num only [agent13004]
  worldRadius := (2289990299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13004]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (562859363 / 500000000000 : ℝ)
  lowerTail := (676984623 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1425803737 / 200000000000 : ℝ)
  ledger := by
    have h : (1159292249 / 1000000000000 : ℚ) +
        (1108391759 / 125000000000000000 : ℚ) / (2289990299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (562859363 / 500000000000 : ℚ) + (676984623 / 500000000000 : ℚ) ≤
        (1425803737 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1159292249 / 1000000000000 : ℚ) +
        (1108391759 / 125000000000000000 : ℚ) / (2289990299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (562859363 / 500000000000 : ℚ) + (676984623 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1425803737 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13004]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13004 :
    2 * 160 < 13004 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999967 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13004 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13005 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13005. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13005 : WorldParameters where
  hiddenCharge := (57962599 / 50000000000 : ℝ)
  frame := (310752599691 / 500000000000 : ℝ)
  moment := (8865353849 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13005 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (366085344047 / 250000000000 : ℝ)
    root := (331863627 / 40000000000 : ℝ) }

noncomputable def scalar13005 : ScalarCertificate 13005 world13005 agent13005 where
  dimensionLo := 13005
  dimensionHi := 13005
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2290352599 / 1000000000000 : ℝ)
  frameLo := (310752599691 / 500000000000 : ℝ)
  frameHi := (366085344047 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13005]
  agentFrame_pos := by norm_num only [agent13005]
  worldRadius := (2290352599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13005]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1124798323 / 1000000000000 : ℝ)
  lowerTail := (16911769 / 12500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7126156013 / 1000000000000 : ℝ)
  ledger := by
    have h : (57962599 / 50000000000 : ℚ) +
        (8865353849 / 1000000000000000000 : ℚ) / (2290352599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1124798323 / 1000000000000 : ℚ) + (16911769 / 12500000000 : ℚ) ≤
        (7126156013 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((57962599 / 50000000000 : ℚ) +
        (8865353849 / 1000000000000000000 : ℚ) / (2290352599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1124798323 / 1000000000000 : ℚ) + (16911769 / 12500000000 : ℚ) : ℚ) : ℝ) ≤
        ((7126156013 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13005]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13005 :
    2 * 160 < 13005 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999607 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13005 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13006 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13006. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13006 : WorldParameters where
  hiddenCharge := (1159211721 / 1000000000000 : ℝ)
  frame := (155373002261 / 250000000000 : ℝ)
  moment := (70908593 / 8000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13006 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (292862432353 / 200000000000 : ℝ)
    root := (8295967017 / 1000000000000 : ℝ) }

noncomputable def scalar13006 : ScalarCertificate 13006 world13006 agent13006 where
  dimensionLo := 13006
  dimensionHi := 13006
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2290715099 / 1000000000000 : ℝ)
  frameLo := (155373002261 / 250000000000 : ℝ)
  frameHi := (292862432353 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13006]
  agentFrame_pos := by norm_num only [agent13006]
  worldRadius := (2290715099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13006]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (280969729 / 250000000000 : ℝ)
  lowerTail := (1351914849 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (890411959 / 125000000000 : ℝ)
  ledger := by
    have h : (1159211721 / 1000000000000 : ℚ) +
        (70908593 / 8000000000000000 : ℚ) / (2290715099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (280969729 / 250000000000 : ℚ) + (1351914849 / 1000000000000 : ℚ) ≤
        (890411959 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1159211721 / 1000000000000 : ℚ) +
        (70908593 / 8000000000000000 : ℚ) / (2290715099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (280969729 / 250000000000 : ℚ) + (1351914849 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((890411959 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13006]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13006 :
    2 * 160 < 13006 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999297 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13006 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13007 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13007. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13007 : WorldParameters where
  hiddenCharge := (1159171473 / 1000000000000 : ℝ)
  frame := (310739410381 / 500000000000 : ℝ)
  moment := (8861794901 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13007 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (732141479637 / 500000000000 : ℝ)
    root := (1659068707 / 200000000000 : ℝ) }

noncomputable def scalar13007 : ScalarCertificate 13007 world13007 agent13007 where
  dimensionLo := 13007
  dimensionHi := 13007
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2291077499 / 1000000000000 : ℝ)
  frameLo := (310739410381 / 500000000000 : ℝ)
  frameHi := (732141479637 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13007]
  agentFrame_pos := by norm_num only [agent13007]
  worldRadius := (2291077499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13007]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (140370037 / 125000000000 : ℝ)
  lowerTail := (1350889 / 1000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3560218831 / 500000000000 : ℝ)
  ledger := by
    have h : (1159171473 / 1000000000000 : ℚ) +
        (8861794901 / 1000000000000000000 : ℚ) / (2291077499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (140370037 / 125000000000 : ℚ) + (1350889 / 1000000000 : ℚ) ≤
        (3560218831 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1159171473 / 1000000000000 : ℚ) +
        (8861794901 / 1000000000000000000 : ℚ) / (2291077499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (140370037 / 125000000000 : ℚ) + (1350889 / 1000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3560218831 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13007]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13007 :
    2 * 160 < 13007 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999741 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13007 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13008 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13008. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13008 : WorldParameters where
  hiddenCharge := (231826247 / 200000000000 : ℝ)
  frame := (77683204317 / 125000000000 : ℝ)
  moment := (354400647 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13008 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (732126887281 / 500000000000 : ℝ)
    root := (8294720229 / 1000000000000 : ℝ) }

noncomputable def scalar13008 : ScalarCertificate 13008 world13008 agent13008 where
  dimensionLo := 13008
  dimensionHi := 13008
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2291440099 / 1000000000000 : ℝ)
  frameLo := (77683204317 / 125000000000 : ℝ)
  frameHi := (732126887281 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13008]
  agentFrame_pos := by norm_num only [agent13008]
  worldRadius := (2291440099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13008]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (280510673 / 250000000000 : ℝ)
  lowerTail := (1349864231 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (889697753 / 125000000000 : ℝ)
  ledger := by
    have h : (231826247 / 200000000000 : ℚ) +
        (354400647 / 40000000000000000 : ℚ) / (2291440099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (280510673 / 250000000000 : ℚ) + (1349864231 / 1000000000000 : ℚ) ≤
        (889697753 / 125000000000 : ℚ) := by norm_num only
    have hc : (((231826247 / 200000000000 : ℚ) +
        (354400647 / 40000000000000000 : ℚ) / (2291440099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (280510673 / 250000000000 : ℚ) + (1349864231 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((889697753 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13008]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13008 :
    2 * 160 < 13008 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999457 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13008 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13009 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13009. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13009 : WorldParameters where
  hiddenCharge := (1159091007 / 1000000000000 : ℝ)
  frame := (155363112591 / 250000000000 : ℝ)
  moment := (8858237949 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13009 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183028075221 / 125000000000 : ℝ)
    root := (8294097097 / 1000000000000 : ℝ) }

noncomputable def scalar13009 : ScalarCertificate 13009 world13009 agent13009 where
  dimensionLo := 13009
  dimensionHi := 13009
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2291802399 / 1000000000000 : ℝ)
  frameLo := (155363112591 / 250000000000 : ℝ)
  frameHi := (183028075221 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13009]
  agentFrame_pos := by norm_num only [agent13009]
  worldRadius := (2291802399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13009]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1121125733 / 1000000000000 : ℝ)
  lowerTail := (1348840127 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7114728713 / 1000000000000 : ℝ)
  ledger := by
    have h : (1159091007 / 1000000000000 : ℚ) +
        (8858237949 / 1000000000000000000 : ℚ) / (2291802399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1121125733 / 1000000000000 : ℚ) + (1348840127 / 1000000000000 : ℚ) ≤
        (7114728713 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1159091007 / 1000000000000 : ℚ) +
        (8858237949 / 1000000000000000000 : ℚ) / (2291802399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1121125733 / 1000000000000 : ℚ) + (1348840127 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7114728713 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13009]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13009 :
    2 * 160 < 13009 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (624999969 / 62500000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13009 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13010 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13010. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13010 : WorldParameters where
  hiddenCharge := (115905079 / 100000000000 : ℝ)
  frame := (77679908531 / 125000000000 : ℝ)
  moment := (8856460221 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13010 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1464117575257 / 1000000000000 : ℝ)
    root := (414673707 / 50000000000 : ℝ) }

noncomputable def scalar13010 : ScalarCertificate 13010 world13010 agent13010 where
  dimensionLo := 13010
  dimensionHi := 13010
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2292281399 / 1000000000000 : ℝ)
  frameLo := (77679908531 / 125000000000 : ℝ)
  frameHi := (1464117575257 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13010]
  agentFrame_pos := by norm_num only [agent13010]
  worldRadius := (2292281399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13010]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1120012121 / 1000000000000 : ℝ)
  lowerTail := (1347557489 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7111249159 / 1000000000000 : ℝ)
  ledger := by
    have h : (115905079 / 100000000000 : ℚ) +
        (8856460221 / 1000000000000000000 : ℚ) / (2292281399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1120012121 / 1000000000000 : ℚ) + (1347557489 / 1000000000000 : ℚ) ≤
        (7111249159 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((115905079 / 100000000000 : ℚ) +
        (8856460221 / 1000000000000000000 : ℚ) / (2292281399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1120012121 / 1000000000000 : ℚ) + (1347557489 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7111249159 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13010]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13010 :
    2 * 160 < 13010 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998039 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13010 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13011 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13011. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13011 : WorldParameters where
  hiddenCharge := (1159010583 / 1000000000000 : ℝ)
  frame := (124285217637 / 200000000000 : ℝ)
  moment := (553417687 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13011 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (292817686601 / 200000000000 : ℝ)
    root := (8292851357 / 1000000000000 : ℝ) }

noncomputable def scalar13011 : ScalarCertificate 13011 world13011 agent13011 where
  dimensionLo := 13011
  dimensionHi := 13011
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2292643799 / 1000000000000 : ℝ)
  frameLo := (124285217637 / 200000000000 : ℝ)
  frameHi := (292817686601 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13011]
  agentFrame_pos := by norm_num only [agent13011]
  worldRadius := (2292643799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13011]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (559548547 / 500000000000 : ℝ)
  lowerTail := (336633861 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (142168019 / 20000000000 : ℝ)
  ledger := by
    have h : (1159010583 / 1000000000000 : ℚ) +
        (553417687 / 62500000000000000 : ℚ) / (2292643799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (559548547 / 500000000000 : ℚ) + (336633861 / 250000000000 : ℚ) ≤
        (142168019 / 20000000000 : ℚ) := by norm_num only
    have hc : (((1159010583 / 1000000000000 : ℚ) +
        (553417687 / 62500000000000000 : ℚ) / (2292643799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (559548547 / 500000000000 : ℚ) + (336633861 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((142168019 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13011]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13011 :
    2 * 160 < 13011 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999909 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13011 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13012 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13012. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13012 : WorldParameters where
  hiddenCharge := (579485193 / 500000000000 : ℝ)
  frame := (24856516407 / 40000000000 : ℝ)
  moment := (8852906261 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13012 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (732029654253 / 500000000000 : ℝ)
    root := (6633783 / 800000000 : ℝ) }

noncomputable def scalar13012 : ScalarCertificate 13012 world13012 agent13012 where
  dimensionLo := 13012
  dimensionHi := 13012
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2293006299 / 1000000000000 : ℝ)
  frameLo := (24856516407 / 40000000000 : ℝ)
  frameHi := (732029654253 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13012]
  agentFrame_pos := by norm_num only [agent13012]
  worldRadius := (2293006299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13012]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (34943219 / 31250000000 : ℝ)
  lowerTail := (1345514397 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7105555107 / 1000000000000 : ℝ)
  ledger := by
    have h : (579485193 / 500000000000 : ℚ) +
        (8852906261 / 1000000000000000000 : ℚ) / (2293006299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (34943219 / 31250000000 : ℚ) + (1345514397 / 1000000000000 : ℚ) ≤
        (7105555107 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((579485193 / 500000000000 : ℚ) +
        (8852906261 / 1000000000000000000 : ℚ) / (2293006299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (34943219 / 31250000000 : ℚ) + (1345514397 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7105555107 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13012]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13012 :
    2 * 160 < 13012 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998479 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13012 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13013 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13013. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13013 : WorldParameters where
  hiddenCharge := (5794651 / 5000000000 : ℝ)
  frame := (621399734219 / 1000000000000 : ℝ)
  moment := (2212782507 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13013 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1464030195897 / 1000000000000 : ℝ)
    root := (8291606317 / 1000000000000 : ℝ) }

noncomputable def scalar13013 : ScalarCertificate 13013 world13013 agent13013 where
  dimensionLo := 13013
  dimensionHi := 13013
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2293368899 / 1000000000000 : ℝ)
  frameLo := (621399734219 / 1000000000000 : ℝ)
  frameHi := (1464030195897 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13013]
  agentFrame_pos := by norm_num only [agent13013]
  worldRadius := (2293368899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13013]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (558634921 / 500000000000 : ℝ)
  lowerTail := (672247161 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (355135579 / 50000000000 : ℝ)
  ledger := by
    have h : (5794651 / 5000000000 : ℚ) +
        (2212782507 / 250000000000000000 : ℚ) / (2293368899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (558634921 / 500000000000 : ℚ) + (672247161 / 500000000000 : ℚ) ≤
        (355135579 / 50000000000 : ℚ) := by norm_num only
    have hc : (((5794651 / 5000000000 : ℚ) +
        (2212782507 / 250000000000000000 : ℚ) / (2293368899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (558634921 / 500000000000 : ℚ) + (672247161 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((355135579 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13013]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13013 :
    2 * 160 < 13013 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999663 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13013 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13014 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13014. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13014 : WorldParameters where
  hiddenCharge := (144861253 / 125000000000 : ℝ)
  frame := (124277312063 / 200000000000 : ℝ)
  moment := (4424677147 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13014 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1464001101027 / 1000000000000 : ℝ)
    root := (1658196799 / 200000000000 : ℝ) }

noncomputable def scalar13014 : ScalarCertificate 13014 world13014 agent13014 where
  dimensionLo := 13014
  dimensionHi := 13014
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2293731399 / 1000000000000 : ℝ)
  frameLo := (124277312063 / 200000000000 : ℝ)
  frameHi := (1464001101027 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13014]
  agentFrame_pos := by norm_num only [agent13014]
  worldRadius := (2293731399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13014]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (223271487 / 200000000000 : ℝ)
  lowerTail := (1343475043 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (283994813 / 40000000000 : ℝ)
  ledger := by
    have h : (144861253 / 125000000000 : ℚ) +
        (4424677147 / 500000000000000000 : ℚ) / (2293731399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (223271487 / 200000000000 : ℚ) + (1343475043 / 1000000000000 : ℚ) ≤
        (283994813 / 40000000000 : ℚ) := by norm_num only
    have hc : (((144861253 / 125000000000 : ℚ) +
        (4424677147 / 500000000000000000 : ℚ) / (2293731399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (223271487 / 200000000000 : ℚ) + (1343475043 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((283994813 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13014]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13014 :
    2 * 160 < 13014 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997213 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13014 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13015 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13015. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13015 : WorldParameters where
  hiddenCharge := (1158849859 / 1000000000000 : ℝ)
  frame := (38835836779 / 62500000000 : ℝ)
  moment := (8847579057 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13015 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1463972012181 / 1000000000000 : ℝ)
    root := (8290361911 / 1000000000000 : ℝ) }

noncomputable def scalar13015 : ScalarCertificate 13015 world13015 agent13015 where
  dimensionLo := 13015
  dimensionHi := 13015
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2294093899 / 1000000000000 : ℝ)
  frameLo := (38835836779 / 62500000000 : ℝ)
  frameHi := (1463972012181 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13015]
  agentFrame_pos := by norm_num only [agent13015]
  worldRadius := (2294093899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13015]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (557722949 / 500000000000 : ℝ)
  lowerTail := (53698267 / 40000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7097031421 / 1000000000000 : ℝ)
  ledger := by
    have h : (1158849859 / 1000000000000 : ℚ) +
        (8847579057 / 1000000000000000000 : ℚ) / (2294093899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (557722949 / 500000000000 : ℚ) + (53698267 / 40000000000 : ℚ) ≤
        (7097031421 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1158849859 / 1000000000000 : ℚ) +
        (8847579057 / 1000000000000000000 : ℚ) / (2294093899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (557722949 / 500000000000 : ℚ) + (53698267 / 40000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7097031421 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13015]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13015 :
    2 * 160 < 13015 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999967 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13015 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13016 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13016. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13016 : WorldParameters where
  hiddenCharge := (144851213 / 125000000000 : ℝ)
  frame := (621360218663 / 1000000000000 : ℝ)
  moment := (4422902159 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13016 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (731971473457 / 500000000000 : ℝ)
    root := (8289740001 / 1000000000000 : ℝ) }

noncomputable def scalar13016 : ScalarCertificate 13016 world13016 agent13016 where
  dimensionLo := 13016
  dimensionHi := 13016
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2294456499 / 1000000000000 : ℝ)
  frameLo := (621360218663 / 1000000000000 : ℝ)
  frameHi := (731971473457 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13016]
  agentFrame_pos := by norm_num only [agent13016]
  worldRadius := (2294456499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13016]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1114535321 / 1000000000000 : ℝ)
  lowerTail := (1341439327 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (177354873 / 25000000000 : ℝ)
  ledger := by
    have h : (144851213 / 125000000000 : ℚ) +
        (4422902159 / 500000000000000000 : ℚ) / (2294456499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1114535321 / 1000000000000 : ℚ) + (1341439327 / 1000000000000 : ℚ) ≤
        (177354873 / 25000000000 : ℚ) := by norm_num only
    have hc : (((144851213 / 125000000000 : ℚ) +
        (4422902159 / 500000000000000000 : ℚ) / (2294456499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1114535321 / 1000000000000 : ℚ) + (1341439327 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((177354873 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13016]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13016 :
    2 * 160 < 13016 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995969 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13016 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13017 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13017. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13017 : WorldParameters where
  hiddenCharge := (1158769559 / 1000000000000 : ℝ)
  frame := (310673525457 / 500000000000 : ℝ)
  moment := (2211007519 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13017 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (182989236689 / 125000000000 : ℝ)
    root := (1657823653 / 200000000000 : ℝ) }

noncomputable def scalar13017 : ScalarCertificate 13017 world13017 agent13017 where
  dimensionLo := 13017
  dimensionHi := 13017
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2294818999 / 1000000000000 : ℝ)
  frameLo := (310673525457 / 500000000000 : ℝ)
  frameHi := (182989236689 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13017]
  agentFrame_pos := by norm_num only [agent13017]
  worldRadius := (2294818999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13017]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1113625521 / 1000000000000 : ℝ)
  lowerTail := (1340422791 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7091360727 / 1000000000000 : ℝ)
  ledger := by
    have h : (1158769559 / 1000000000000 : ℚ) +
        (2211007519 / 250000000000000000 : ℚ) / (2294818999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1113625521 / 1000000000000 : ℚ) + (1340422791 / 1000000000000 : ℚ) ≤
        (7091360727 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1158769559 / 1000000000000 : ℚ) +
        (2211007519 / 250000000000000000 : ℚ) / (2294818999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1113625521 / 1000000000000 : ℚ) + (1340422791 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7091360727 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13017]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13017 :
    2 * 160 < 13017 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499998667 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13017 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13018 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13018. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13018 : WorldParameters where
  hiddenCharge := (46349177 / 40000000000 : ℝ)
  frame := (124266777043 / 200000000000 : ℝ)
  moment := (8842256331 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13018 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1463884851967 / 1000000000000 : ℝ)
    root := (8288496703 / 1000000000000 : ℝ) }

noncomputable def scalar13018 : ScalarCertificate 13018 world13018 agent13018 where
  dimensionLo := 13018
  dimensionHi := 13018
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2295181599 / 1000000000000 : ℝ)
  frameLo := (124266777043 / 200000000000 : ℝ)
  frameHi := (1463884851967 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13018]
  agentFrame_pos := by norm_num only [agent13018]
  worldRadius := (2295181599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13018]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (278179159 / 250000000000 : ℝ)
  lowerTail := (669703611 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1772132209 / 250000000000 : ℝ)
  ledger := by
    have h : (46349177 / 40000000000 : ℚ) +
        (8842256331 / 1000000000000000000 : ℚ) / (2295181599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (278179159 / 250000000000 : ℚ) + (669703611 / 500000000000 : ℚ) ≤
        (1772132209 / 250000000000 : ℚ) := by norm_num only
    have hc : (((46349177 / 40000000000 : ℚ) +
        (8842256331 / 1000000000000000000 : ℚ) / (2295181599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (278179159 / 250000000000 : ℚ) + (669703611 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1772132209 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13018]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13018 :
    2 * 160 < 13018 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (39999983 / 4000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13018 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13019 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13019. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13019 : WorldParameters where
  hiddenCharge := (1158689301 / 1000000000000 : ℝ)
  frame := (621320721567 / 1000000000000 : ℝ)
  moment := (2210120771 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13019 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58554232891 / 40000000000 : ℝ)
    root := (1657575063 / 200000000000 : ℝ) }

noncomputable def scalar13019 : ScalarCertificate 13019 world13019 agent13019 where
  dimensionLo := 13019
  dimensionHi := 13019
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2295544099 / 1000000000000 : ℝ)
  frameLo := (621320721567 / 1000000000000 : ℝ)
  frameHi := (58554232891 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13019]
  agentFrame_pos := by norm_num only [agent13019]
  worldRadius := (2295544099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13019]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1111808527 / 1000000000000 : ℝ)
  lowerTail := (83649529 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7085699249 / 1000000000000 : ℝ)
  ledger := by
    have h : (1158689301 / 1000000000000 : ℚ) +
        (2210120771 / 250000000000000000 : ℚ) / (2295544099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1111808527 / 1000000000000 : ℚ) + (83649529 / 62500000000 : ℚ) ≤
        (7085699249 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1158689301 / 1000000000000 : ℚ) +
        (2210120771 / 250000000000000000 : ℚ) / (2295544099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1111808527 / 1000000000000 : ℚ) + (83649529 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((7085699249 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13019]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13019 :
    2 * 160 < 13019 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999199 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13019 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13020 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13020. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13020 : WorldParameters where
  hiddenCharge := (1158649187 / 1000000000000 : ℝ)
  frame := (621307559967 / 1000000000000 : ℝ)
  moment := (8838710333 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13020 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (731874524129 / 500000000000 : ℝ)
    root := (8287254101 / 1000000000000 : ℝ) }

noncomputable def scalar13020 : ScalarCertificate 13020 world13020 agent13020 where
  dimensionLo := 13020
  dimensionHi := 13020
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2296023199 / 1000000000000 : ℝ)
  frameLo := (621307559967 / 1000000000000 : ℝ)
  frameHi := (731874524129 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13020]
  agentFrame_pos := by norm_num only [agent13020]
  worldRadius := (2296023199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13020]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1110705401 / 1000000000000 : ℝ)
  lowerTail := (133712119 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7082248393 / 1000000000000 : ℝ)
  ledger := by
    have h : (1158649187 / 1000000000000 : ℚ) +
        (8838710333 / 1000000000000000000 : ℚ) / (2296023199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1110705401 / 1000000000000 : ℚ) + (133712119 / 100000000000 : ℚ) ≤
        (7082248393 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1158649187 / 1000000000000 : ℚ) +
        (8838710333 / 1000000000000000000 : ℚ) / (2296023199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1110705401 / 1000000000000 : ℚ) + (133712119 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7082248393 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13020]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13020 :
    2 * 160 < 13020 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999861 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13020 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13021 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13021. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13021 : WorldParameters where
  hiddenCharge := (289652271 / 250000000000 : ℝ)
  frame := (621294400417 / 1000000000000 : ℝ)
  moment := (8836938079 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13021 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (731860027411 / 500000000000 : ℝ)
    root := (4143316499 / 500000000000 : ℝ) }

noncomputable def scalar13021 : ScalarCertificate 13021 world13021 agent13021 where
  dimensionLo := 13021
  dimensionHi := 13021
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2296385799 / 1000000000000 : ℝ)
  frameLo := (621294400417 / 1000000000000 : ℝ)
  frameHi := (731860027411 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13021]
  agentFrame_pos := by norm_num only [agent13021]
  worldRadius := (2296385799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13021]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1109799181 / 1000000000000 : ℝ)
  lowerTail := (334027113 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7079423819 / 1000000000000 : ℝ)
  ledger := by
    have h : (289652271 / 250000000000 : ℚ) +
        (8836938079 / 1000000000000000000 : ℚ) / (2296385799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1109799181 / 1000000000000 : ℚ) + (334027113 / 250000000000 : ℚ) ≤
        (7079423819 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((289652271 / 250000000000 : ℚ) +
        (8836938079 / 1000000000000000000 : ℚ) / (2296385799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1109799181 / 1000000000000 : ℚ) + (334027113 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7079423819 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13021]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13021 :
    2 * 160 < 13021 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998023 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13021 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13022 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13022. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13022 : WorldParameters where
  hiddenCharge := (1158568991 / 1000000000000 : ℝ)
  frame := (124256248583 / 200000000000 : ℝ)
  moment := (4417583161 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13022 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1463691073217 / 1000000000000 : ℝ)
    root := (8286012131 / 1000000000000 : ℝ) }

noncomputable def scalar13022 : ScalarCertificate 13022 world13022 agent13022 where
  dimensionLo := 13022
  dimensionHi := 13022
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2296748399 / 1000000000000 : ℝ)
  frameLo := (124256248583 / 200000000000 : ℝ)
  frameHi := (1463691073217 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13022]
  agentFrame_pos := by norm_num only [agent13022]
  worldRadius := (2296748399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13022]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (221778769 / 200000000000 : ℝ)
  lowerTail := (1335096643 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (56612813 / 8000000000 : ℝ)
  ledger := by
    have h : (1158568991 / 1000000000000 : ℚ) +
        (4417583161 / 500000000000000000 : ℚ) / (2296748399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (221778769 / 200000000000 : ℚ) + (1335096643 / 1000000000000 : ℚ) ≤
        (56612813 / 8000000000 : ℚ) := by norm_num only
    have hc : (((1158568991 / 1000000000000 : ℚ) +
        (4417583161 / 500000000000000000 : ℚ) / (2296748399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (221778769 / 200000000000 : ℚ) + (1335096643 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((56612813 / 8000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13022]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13022 :
    2 * 160 < 13022 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999387 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13022 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13023 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13023. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13023 : WorldParameters where
  hiddenCharge := (289632227 / 250000000000 : ℝ)
  frame := (31063404373 / 50000000000 : ℝ)
  moment := (8833395061 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13023 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1463662103437 / 1000000000000 : ℝ)
    root := (4142695719 / 500000000000 : ℝ) }

noncomputable def scalar13023 : ScalarCertificate 13023 world13023 agent13023 where
  dimensionLo := 13023
  dimensionHi := 13023
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2297110999 / 1000000000000 : ℝ)
  frameLo := (31063404373 / 50000000000 : ℝ)
  frameHi := (1463662103437 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13023]
  agentFrame_pos := by norm_num only [agent13023]
  worldRadius := (2297110999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13023]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1107989351 / 1000000000000 : ℝ)
  lowerTail := (1334085719 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (282951269 / 40000000000 : ℝ)
  ledger := by
    have h : (289632227 / 250000000000 : ℚ) +
        (8833395061 / 1000000000000000000 : ℚ) / (2297110999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1107989351 / 1000000000000 : ℚ) + (1334085719 / 1000000000000 : ℚ) ≤
        (282951269 / 40000000000 : ℚ) := by norm_num only
    have hc : (((289632227 / 250000000000 : ℚ) +
        (8833395061 / 1000000000000000000 : ℚ) / (2297110999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1107989351 / 1000000000000 : ℚ) + (1334085719 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((282951269 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13023]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13023 :
    2 * 160 < 13023 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998219 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13023 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 13024 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 13024. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world13024 : WorldParameters where
  hiddenCharge := (289622209 / 250000000000 : ℝ)
  frame := (310627467027 / 500000000000 : ℝ)
  moment := (1103953037 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent13024 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (45738535979 / 31250000000 : ℝ)
    root := (4142385459 / 500000000000 : ℝ) }

noncomputable def scalar13024 : ScalarCertificate 13024 world13024 agent13024 where
  dimensionLo := 13024
  dimensionHi := 13024
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2297473699 / 1000000000000 : ℝ)
  frameLo := (310627467027 / 500000000000 : ℝ)
  frameHi := (45738535979 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world13024]
  agentFrame_pos := by norm_num only [agent13024]
  worldRadius := (2297473699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent13024]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1107085787 / 1000000000000 : ℝ)
  lowerTail := (1333075781 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3535482081 / 500000000000 : ℝ)
  ledger := by
    have h : (289622209 / 250000000000 : ℚ) +
        (1103953037 / 125000000000000000 : ℚ) / (2297473699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1107085787 / 1000000000000 : ℚ) + (1333075781 / 1000000000000 : ℚ) ≤
        (3535482081 / 500000000000 : ℚ) := by norm_num only
    have hc : (((289622209 / 250000000000 : ℚ) +
        (1103953037 / 125000000000000000 : ℚ) / (2297473699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1107085787 / 1000000000000 : ℚ) + (1333075781 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3535482081 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world13024]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards13024 :
    2 * 160 < 13024 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999998871 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 13024 {← IO.monoMsNow}" : IO Unit)
