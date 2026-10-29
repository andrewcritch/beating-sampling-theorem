import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12850 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12850. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12850 : WorldParameters where
  hiddenCharge := (1165620063 / 1000000000000 : ℝ)
  frame := (12471497759 / 20000000000 : ℝ)
  moment := (9147362571 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12850 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183770567137 / 125000000000 : ℝ)
    root := (8395440267 / 1000000000000 : ℝ) }

noncomputable def scalar12850 : ScalarCertificate 12850 world12850 agent12850 where
  dimensionLo := 12850
  dimensionHi := 12850
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2232649099 / 1000000000000 : ℝ)
  frameLo := (12471497759 / 20000000000 : ℝ)
  frameHi := (183770567137 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12850]
  agentFrame_pos := by norm_num only [agent12850]
  worldRadius := (2232649099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12850]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (80103649 / 62500000000 : ℝ)
  lowerTail := (763971301 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7609446827 / 1000000000000 : ℝ)
  ledger := by
    have h : (1165620063 / 1000000000000 : ℚ) +
        (9147362571 / 1000000000000000000 : ℚ) / (2232649099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (80103649 / 62500000000 : ℚ) + (763971301 / 500000000000 : ℚ) ≤
        (7609446827 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1165620063 / 1000000000000 : ℚ) +
        (9147362571 / 1000000000000000000 : ℚ) / (2232649099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (80103649 / 62500000000 : ℚ) + (763971301 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7609446827 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12850]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12850 :
    2 * 160 < 12850 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998231 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12850 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12851 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12851. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12851 : WorldParameters where
  hiddenCharge := (1165578149 / 1000000000000 : ℝ)
  frame := (623561372621 / 1000000000000 : ℝ)
  moment := (9145503241 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12851 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735066936007 / 500000000000 : ℝ)
    root := (419739409 / 50000000000 : ℝ) }

noncomputable def scalar12851 : ScalarCertificate 12851 world12851 agent12851 where
  dimensionLo := 12851
  dimensionHi := 12851
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2233008899 / 1000000000000 : ℝ)
  frameLo := (623561372621 / 1000000000000 : ℝ)
  frameHi := (735066936007 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12851]
  agentFrame_pos := by norm_num only [agent12851]
  worldRadius := (2233008899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12851]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (640296021 / 500000000000 : ℝ)
  lowerTail := (7633811 / 5000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3803096983 / 500000000000 : ℝ)
  ledger := by
    have h : (1165578149 / 1000000000000 : ℚ) +
        (9145503241 / 1000000000000000000 : ℚ) / (2233008899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (640296021 / 500000000000 : ℚ) + (7633811 / 5000000000 : ℚ) ≤
        (3803096983 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1165578149 / 1000000000000 : ℚ) +
        (9145503241 / 1000000000000000000 : ℚ) / (2233008899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (640296021 / 500000000000 : ℚ) + (7633811 / 5000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3803096983 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12851]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12851 :
    2 * 160 < 12851 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997357 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12851 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12852 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12852. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12852 : WorldParameters where
  hiddenCharge := (582768123 / 500000000000 : ℝ)
  frame := (623547859431 / 1000000000000 : ℝ)
  moment := (9143644439 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12852 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470103225827 / 1000000000000 : ℝ)
    root := (8394136287 / 1000000000000 : ℝ) }

noncomputable def scalar12852 : ScalarCertificate 12852 world12852 agent12852 where
  dimensionLo := 12852
  dimensionHi := 12852
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2233368699 / 1000000000000 : ℝ)
  frameLo := (623547859431 / 1000000000000 : ℝ)
  frameHi := (1470103225827 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12852]
  agentFrame_pos := by norm_num only [agent12852]
  worldRadius := (2233368699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12852]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1279526739 / 1000000000000 : ℝ)
  lowerTail := (1525582883 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (59397999 / 7812500000 : ℝ)
  ledger := by
    have h : (582768123 / 500000000000 : ℚ) +
        (9143644439 / 1000000000000000000 : ℚ) / (2233368699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1279526739 / 1000000000000 : ℚ) + (1525582883 / 1000000000000 : ℚ) ≤
        (59397999 / 7812500000 : ℚ) := by norm_num only
    have hc : (((582768123 / 500000000000 : ℚ) +
        (9143644439 / 1000000000000000000 : ℚ) / (2233368699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1279526739 / 1000000000000 : ℚ) + (1525582883 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((59397999 / 7812500000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12852]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12852 :
    2 * 160 < 12852 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999453 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12852 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12853 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12853. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12853 : WorldParameters where
  hiddenCharge := (582747177 / 500000000000 : ℝ)
  frame := (623534348377 / 1000000000000 : ℝ)
  moment := (1828357233 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12853 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470072592637 / 1000000000000 : ℝ)
    root := (8393484587 / 1000000000000 : ℝ) }

noncomputable def scalar12853 : ScalarCertificate 12853 world12853 agent12853 where
  dimensionLo := 12853
  dimensionHi := 12853
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2233728499 / 1000000000000 : ℝ)
  frameLo := (623534348377 / 1000000000000 : ℝ)
  frameHi := (1470072592637 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12853]
  agentFrame_pos := by norm_num only [agent12853]
  worldRadius := (2233728499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12853]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1278462449 / 1000000000000 : ℝ)
  lowerTail := (762202311 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7599696489 / 1000000000000 : ℝ)
  ledger := by
    have h : (582747177 / 500000000000 : ℚ) +
        (1828357233 / 200000000000000000 : ℚ) / (2233728499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1278462449 / 1000000000000 : ℚ) + (762202311 / 500000000000 : ℚ) ≤
        (7599696489 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((582747177 / 500000000000 : ℚ) +
        (1828357233 / 200000000000000000 : ℚ) / (2233728499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1278462449 / 1000000000000 : ℚ) + (762202311 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7599696489 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12853]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12853 :
    2 * 160 < 12853 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999213 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12853 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12854 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12854. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12854 : WorldParameters where
  hiddenCharge := (1165452473 / 1000000000000 : ℝ)
  frame := (31176041973 / 50000000000 : ℝ)
  moment := (9139928419 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12854 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58801679133 / 40000000000 : ℝ)
    root := (8392833079 / 1000000000000 : ℝ) }

noncomputable def scalar12854 : ScalarCertificate 12854 world12854 agent12854 where
  dimensionLo := 12854
  dimensionHi := 12854
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2234088199 / 1000000000000 : ℝ)
  frameLo := (31176041973 / 50000000000 : ℝ)
  frameHi := (58801679133 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12854]
  agentFrame_pos := by norm_num only [agent12854]
  worldRadius := (2234088199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12854]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1277399117 / 1000000000000 : ℝ)
  lowerTail := (1523227357 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1899112967 / 250000000000 : ℝ)
  ledger := by
    have h : (1165452473 / 1000000000000 : ℚ) +
        (9139928419 / 1000000000000000000 : ℚ) / (2234088199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1277399117 / 1000000000000 : ℚ) + (1523227357 / 1000000000000 : ℚ) ≤
        (1899112967 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1165452473 / 1000000000000 : ℚ) +
        (9139928419 / 1000000000000000000 : ℚ) / (2234088199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1277399117 / 1000000000000 : ℚ) + (1523227357 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1899112967 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12854]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12854 :
    2 * 160 < 12854 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (624999713 / 62500000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12854 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12855 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12855. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12855 : WorldParameters where
  hiddenCharge := (1165410603 / 1000000000000 : ℝ)
  frame := (311753666339 / 500000000000 : ℝ)
  moment := (11422589 / 1250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12855 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735005688497 / 500000000000 : ℝ)
    root := (8392181763 / 1000000000000 : ℝ) }

noncomputable def scalar12855 : ScalarCertificate 12855 world12855 agent12855 where
  dimensionLo := 12855
  dimensionHi := 12855
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2234448099 / 1000000000000 : ℝ)
  frameLo := (311753666339 / 500000000000 : ℝ)
  frameHi := (735005688497 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12855]
  agentFrame_pos := by norm_num only [agent12855]
  worldRadius := (2234448099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12855]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (159542119 / 125000000000 : ℝ)
  lowerTail := (761025659 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (151864199 / 20000000000 : ℝ)
  ledger := by
    have h : (1165410603 / 1000000000000 : ℚ) +
        (11422589 / 1250000000000000 : ℚ) / (2234448099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (159542119 / 125000000000 : ℚ) + (761025659 / 500000000000 : ℚ) ≤
        (151864199 / 20000000000 : ℚ) := by norm_num only
    have hc : (((1165410603 / 1000000000000 : ℚ) +
        (11422589 / 1250000000000000 : ℚ) / (2234448099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (159542119 / 125000000000 : ℚ) + (761025659 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((151864199 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12855]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12855 :
    2 * 160 < 12855 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998443 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12855 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12856 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12856. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12856 : WorldParameters where
  hiddenCharge := (145671093 / 125000000000 : ℝ)
  frame := (9742091063 / 15625000000 : ℝ)
  moment := (2284053627 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12856 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58799231781 / 40000000000 : ℝ)
    root := (104894133 / 12500000000 : ℝ) }

noncomputable def scalar12856 : ScalarCertificate 12856 world12856 agent12856 where
  dimensionLo := 12856
  dimensionHi := 12856
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2234807799 / 1000000000000 : ℝ)
  frameLo := (9742091063 / 15625000000 : ℝ)
  frameHi := (58799231781 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12856]
  agentFrame_pos := by norm_num only [agent12856]
  worldRadius := (2234807799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12856]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (79704729 / 62500000000 : ℝ)
  lowerTail := (380219047 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7589970789 / 1000000000000 : ℝ)
  ledger := by
    have h : (145671093 / 125000000000 : ℚ) +
        (2284053627 / 250000000000000000 : ℚ) / (2234807799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (79704729 / 62500000000 : ℚ) + (380219047 / 250000000000 : ℚ) ≤
        (7589970789 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((145671093 / 125000000000 : ℚ) +
        (2284053627 / 250000000000000000 : ℚ) / (2234807799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (79704729 / 62500000000 : ℚ) + (380219047 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7589970789 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12856]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12856 :
    2 * 160 < 12856 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995649 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12856 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12857 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12857. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12857 : WorldParameters where
  hiddenCharge := (72832931 / 62500000000 : ℝ)
  frame := (623480325521 / 1000000000000 : ℝ)
  moment := (9134358343 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12857 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (734975112511 / 500000000000 : ℝ)
    root := (8390879709 / 1000000000000 : ℝ) }

noncomputable def scalar12857 : ScalarCertificate 12857 world12857 agent12857 where
  dimensionLo := 12857
  dimensionHi := 12857
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2235167699 / 1000000000000 : ℝ)
  frameLo := (623480325521 / 1000000000000 : ℝ)
  frameHi := (734975112511 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12857]
  agentFrame_pos := by norm_num only [agent12857]
  worldRadius := (2235167699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12857]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1274215541 / 1000000000000 : ℝ)
  lowerTail := (1519702281 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (948341791 / 125000000000 : ℝ)
  ledger := by
    have h : (72832931 / 62500000000 : ℚ) +
        (9134358343 / 1000000000000000000 : ℚ) / (2235167699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1274215541 / 1000000000000 : ℚ) + (1519702281 / 1000000000000 : ℚ) ≤
        (948341791 / 125000000000 : ℚ) := by norm_num only
    have hc : (((72832931 / 62500000000 : ℚ) +
        (9134358343 / 1000000000000000000 : ℚ) / (2235167699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1274215541 / 1000000000000 : ℚ) + (1519702281 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((948341791 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12857]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12857 :
    2 * 160 < 12857 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997293 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12857 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12858 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12858. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12858 : WorldParameters where
  hiddenCharge := (1165285059 / 1000000000000 : ℝ)
  frame := (77933353143 / 125000000000 : ℝ)
  moment := (4566251353 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12858 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367479918591 / 250000000000 : ℝ)
    root := (8390228969 / 1000000000000 : ℝ) }

noncomputable def scalar12858 : ScalarCertificate 12858 world12858 agent12858 where
  dimensionLo := 12858
  dimensionHi := 12858
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2235527499 / 1000000000000 : ℝ)
  frameLo := (77933353143 / 125000000000 : ℝ)
  frameHi := (367479918591 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12858]
  agentFrame_pos := by norm_num only [agent12858]
  worldRadius := (2235527499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12858]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1273156371 / 1000000000000 : ℝ)
  lowerTail := (759264683 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1516700123 / 200000000000 : ℝ)
  ledger := by
    have h : (1165285059 / 1000000000000 : ℚ) +
        (4566251353 / 500000000000000000 : ℚ) / (2235527499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1273156371 / 1000000000000 : ℚ) + (759264683 / 500000000000 : ℚ) ≤
        (1516700123 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1165285059 / 1000000000000 : ℚ) +
        (4566251353 / 500000000000000000 : ℚ) / (2235527499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1273156371 / 1000000000000 : ℚ) + (759264683 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1516700123 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12858]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12858 :
    2 * 160 < 12858 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996179 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12858 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12859 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12859. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12859 : WorldParameters where
  hiddenCharge := (1165243233 / 1000000000000 : ℝ)
  frame := (623453326901 / 1000000000000 : ℝ)
  moment := (1826129519 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12859 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (91868071041 / 62500000000 : ℝ)
    root := (4194789211 / 500000000000 : ℝ) }

noncomputable def scalar12859 : ScalarCertificate 12859 world12859 agent12859 where
  dimensionLo := 12859
  dimensionHi := 12859
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2235887299 / 1000000000000 : ℝ)
  frameLo := (623453326901 / 1000000000000 : ℝ)
  frameHi := (91868071041 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12859]
  agentFrame_pos := by norm_num only [agent12859]
  worldRadius := (2235887299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12859]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (39753069 / 31250000000 : ℝ)
  lowerTail := (606943 / 400000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3790134799 / 500000000000 : ℝ)
  ledger := by
    have h : (1165243233 / 1000000000000 : ℚ) +
        (1826129519 / 200000000000000000 : ℚ) / (2235887299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (39753069 / 31250000000 : ℚ) + (606943 / 400000000 : ℚ) ≤
        (3790134799 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1165243233 / 1000000000000 : ℚ) +
        (1826129519 / 200000000000000000 : ℚ) / (2235887299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (39753069 / 31250000000 : ℚ) + (606943 / 400000000 : ℚ) : ℚ) : ℝ) ≤
        ((3790134799 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12859]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12859 :
    2 * 160 < 12859 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997907 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12859 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12860 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12860. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12860 : WorldParameters where
  hiddenCharge := (1165201417 / 1000000000000 : ℝ)
  frame := (623439830791 / 1000000000000 : ℝ)
  moment := (9128793011 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12860 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1469779073191 / 1000000000000 : ℝ)
    root := (8388928067 / 1000000000000 : ℝ) }

noncomputable def scalar12860 : ScalarCertificate 12860 world12860 agent12860 where
  dimensionLo := 12860
  dimensionHi := 12860
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2236361599 / 1000000000000 : ℝ)
  frameLo := (623439830791 / 1000000000000 : ℝ)
  frameHi := (1469779073191 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12860]
  agentFrame_pos := by norm_num only [agent12860]
  worldRadius := (2236361599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12860]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1270814057 / 1000000000000 : ℝ)
  lowerTail := (1515891427 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3788166053 / 500000000000 : ℝ)
  ledger := by
    have h : (1165201417 / 1000000000000 : ℚ) +
        (9128793011 / 1000000000000000000 : ℚ) / (2236361599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1270814057 / 1000000000000 : ℚ) + (1515891427 / 1000000000000 : ℚ) ≤
        (3788166053 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1165201417 / 1000000000000 : ℚ) +
        (9128793011 / 1000000000000000000 : ℚ) / (2236361599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1270814057 / 1000000000000 : ℚ) + (1515891427 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3788166053 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12860]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12860 :
    2 * 160 < 12860 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996833 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12860 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12861 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12861. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12861 : WorldParameters where
  hiddenCharge := (1165159613 / 1000000000000 : ℝ)
  frame := (311713168407 / 500000000000 : ℝ)
  moment := (9126938953 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12861 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (734874284079 / 500000000000 : ℝ)
    root := (8388277839 / 1000000000000 : ℝ) }

noncomputable def scalar12861 : ScalarCertificate 12861 world12861 agent12861 where
  dimensionLo := 12861
  dimensionHi := 12861
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2236721499 / 1000000000000 : ℝ)
  frameLo := (311713168407 / 500000000000 : ℝ)
  frameHi := (734874284079 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12861]
  agentFrame_pos := by norm_num only [agent12861]
  worldRadius := (2236721499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12861]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1269758111 / 1000000000000 : ℝ)
  lowerTail := (1514721907 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7573106893 / 1000000000000 : ℝ)
  ledger := by
    have h : (1165159613 / 1000000000000 : ℚ) +
        (9126938953 / 1000000000000000000 : ℚ) / (2236721499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1269758111 / 1000000000000 : ℚ) + (1514721907 / 1000000000000 : ℚ) ≤
        (7573106893 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1165159613 / 1000000000000 : ℚ) +
        (9126938953 / 1000000000000000000 : ℚ) / (2236721499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1269758111 / 1000000000000 : ℚ) + (1514721907 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7573106893 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12861]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12861 :
    2 * 160 < 12861 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998563 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12861 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12862 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12862. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12862 : WorldParameters where
  hiddenCharge := (1165117819 / 1000000000000 : ℝ)
  frame := (623412844969 / 1000000000000 : ℝ)
  moment := (9125085421 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12862 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (734859040969 / 500000000000 : ℝ)
    root := (8387627867 / 1000000000000 : ℝ) }

noncomputable def scalar12862 : ScalarCertificate 12862 world12862 agent12862 where
  dimensionLo := 12862
  dimensionHi := 12862
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2237081399 / 1000000000000 : ℝ)
  frameLo := (623412844969 / 1000000000000 : ℝ)
  frameHi := (734859040969 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12862]
  agentFrame_pos := by norm_num only [agent12862]
  worldRadius := (2237081399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12862]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1268703241 / 1000000000000 : ℝ)
  lowerTail := (1513553511 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (189247113 / 25000000000 : ℝ)
  ledger := by
    have h : (1165117819 / 1000000000000 : ℚ) +
        (9125085421 / 1000000000000000000 : ℚ) / (2237081399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1268703241 / 1000000000000 : ℚ) + (1513553511 / 1000000000000 : ℚ) ≤
        (189247113 / 25000000000 : ℚ) := by norm_num only
    have hc : (((1165117819 / 1000000000000 : ℚ) +
        (9125085421 / 1000000000000000000 : ℚ) / (2237081399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1268703241 / 1000000000000 : ℚ) + (1513553511 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((189247113 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12862]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12862 :
    2 * 160 < 12862 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997447 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12862 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12863 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12863. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12863 : WorldParameters where
  hiddenCharge := (1165076037 / 1000000000000 : ℝ)
  frame := (77924919407 / 125000000000 : ℝ)
  moment := (1824646483 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12863 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (293937521727 / 200000000000 : ℝ)
    root := (4193489043 / 500000000000 : ℝ) }

noncomputable def scalar12863 : ScalarCertificate 12863 world12863 agent12863 where
  dimensionLo := 12863
  dimensionHi := 12863
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2237441299 / 1000000000000 : ℝ)
  frameLo := (77924919407 / 125000000000 : ℝ)
  frameHi := (293937521727 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12863]
  agentFrame_pos := by norm_num only [agent12863]
  worldRadius := (2237441299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12863]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (633824687 / 500000000000 : ℝ)
  lowerTail := (756193079 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7566664829 / 1000000000000 : ℝ)
  ledger := by
    have h : (1165076037 / 1000000000000 : ℚ) +
        (1824646483 / 200000000000000000 : ℚ) / (2237441299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (633824687 / 500000000000 : ℚ) + (756193079 / 500000000000 : ℚ) ≤
        (7566664829 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1165076037 / 1000000000000 : ℚ) +
        (1824646483 / 200000000000000000 : ℚ) / (2237441299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (633824687 / 500000000000 : ℚ) + (756193079 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7566664829 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12863]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12863 :
    2 * 160 < 12863 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999887 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12863 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12864 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12864. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12864 : WorldParameters where
  hiddenCharge := (233006853 / 200000000000 : ℝ)
  frame := (623385867673 / 1000000000000 : ℝ)
  moment := (1824275987 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12864 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1469657154129 / 1000000000000 : ℝ)
    root := (8386328497 / 1000000000000 : ℝ) }

noncomputable def scalar12864 : ScalarCertificate 12864 world12864 agent12864 where
  dimensionLo := 12864
  dimensionHi := 12864
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2237801199 / 1000000000000 : ℝ)
  frameLo := (623385867673 / 1000000000000 : ℝ)
  frameHi := (1469657154129 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12864]
  agentFrame_pos := by norm_num only [agent12864]
  worldRadius := (2237801199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12864]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (126659653 / 100000000000 : ℝ)
  lowerTail := (755609939 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (118178873 / 15625000000 : ℝ)
  ledger := by
    have h : (233006853 / 200000000000 : ℚ) +
        (1824275987 / 200000000000000000 : ℚ) / (2237801199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (126659653 / 100000000000 : ℚ) + (755609939 / 500000000000 : ℚ) ≤
        (118178873 / 15625000000 : ℚ) := by norm_num only
    have hc : (((233006853 / 200000000000 : ℚ) +
        (1824275987 / 200000000000000000 : ℚ) / (2237801199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (126659653 / 100000000000 : ℚ) + (755609939 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((118178873 / 15625000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12864]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12864 :
    2 * 160 < 12864 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997857 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12864 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12865 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12865. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12865 : WorldParameters where
  hiddenCharge := (232998501 / 200000000000 : ℝ)
  frame := (311686191111 / 500000000000 : ℝ)
  moment := (9119527981 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12865 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58785068501 / 40000000000 : ℝ)
    root := (8385679099 / 1000000000000 : ℝ) }

noncomputable def scalar12865 : ScalarCertificate 12865 world12865 agent12865 where
  dimensionLo := 12865
  dimensionHi := 12865
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2238161099 / 1000000000000 : ℝ)
  frameLo := (311686191111 / 500000000000 : ℝ)
  frameHi := (58785068501 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12865]
  agentFrame_pos := by norm_num only [agent12865]
  worldRadius := (2238161099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12865]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (632772343 / 500000000000 : ℝ)
  lowerTail := (1510054639 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3780116797 / 500000000000 : ℝ)
  ledger := by
    have h : (232998501 / 200000000000 : ℚ) +
        (9119527981 / 1000000000000000000 : ℚ) / (2238161099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (632772343 / 500000000000 : ℚ) + (1510054639 / 1000000000000 : ℚ) ≤
        (3780116797 / 500000000000 : ℚ) := by norm_num only
    have hc : (((232998501 / 200000000000 : ℚ) +
        (9119527981 / 1000000000000000000 : ℚ) / (2238161099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (632772343 / 500000000000 : ℚ) + (1510054639 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3780116797 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12865]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12865 :
    2 * 160 < 12865 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999343 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12865 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12866 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12866. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12866 : WorldParameters where
  hiddenCharge := (232990151 / 200000000000 : ℝ)
  frame := (6233588989 / 10000000000 : ℝ)
  moment := (9117676551 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12866 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1469596289701 / 1000000000000 : ℝ)
    root := (2096257473 / 250000000000 : ℝ) }

noncomputable def scalar12866 : ScalarCertificate 12866 world12866 agent12866 where
  dimensionLo := 12866
  dimensionHi := 12866
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2238520899 / 1000000000000 : ℝ)
  frameLo := (6233588989 / 10000000000 : ℝ)
  frameHi := (1469596289701 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12866]
  agentFrame_pos := by norm_num only [agent12866]
  worldRadius := (2238520899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12866]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1264493787 / 1000000000000 : ℝ)
  lowerTail := (94305649 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7557022041 / 1000000000000 : ℝ)
  ledger := by
    have h : (232990151 / 200000000000 : ℚ) +
        (9117676551 / 1000000000000000000 : ℚ) / (2238520899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1264493787 / 1000000000000 : ℚ) + (94305649 / 62500000000 : ℚ) ≤
        (7557022041 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((232990151 / 200000000000 : ℚ) +
        (9117676551 / 1000000000000000000 : ℚ) / (2238520899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1264493787 / 1000000000000 : ℚ) + (94305649 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((7557022041 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12866]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12866 :
    2 * 160 < 12866 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997899 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12866 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12867 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12867. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12867 : WorldParameters where
  hiddenCharge := (145613627 / 125000000000 : ℝ)
  frame := (623345417707 / 1000000000000 : ℝ)
  moment := (569739103 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12867 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367391469941 / 250000000000 : ℝ)
    root := (2096095219 / 250000000000 : ℝ) }

noncomputable def scalar12867 : ScalarCertificate 12867 world12867 agent12867 where
  dimensionLo := 12867
  dimensionHi := 12867
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2238880699 / 1000000000000 : ℝ)
  frameLo := (623345417707 / 1000000000000 : ℝ)
  frameHi := (367391469941 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12867]
  agentFrame_pos := by norm_num only [agent12867]
  worldRadius := (2238880699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12867]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (252688777 / 200000000000 : ℝ)
  lowerTail := (1507727169 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7553813161 / 1000000000000 : ℝ)
  ledger := by
    have h : (145613627 / 125000000000 : ℚ) +
        (569739103 / 62500000000000000 : ℚ) / (2238880699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (252688777 / 200000000000 : ℚ) + (1507727169 / 1000000000000 : ℚ) ≤
        (7553813161 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((145613627 / 125000000000 : ℚ) +
        (569739103 / 62500000000000000 : ℚ) / (2238880699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (252688777 / 200000000000 : ℚ) + (1507727169 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7553813161 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12867]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12867 :
    2 * 160 < 12867 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999141 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12867 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12868 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12868. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12868 : WorldParameters where
  hiddenCharge := (145608411 / 125000000000 : ℝ)
  frame := (155832984661 / 250000000000 : ℝ)
  moment := (9113975269 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12868 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1469535488591 / 1000000000000 : ℝ)
    root := (8383732051 / 1000000000000 : ℝ) }

noncomputable def scalar12868 : ScalarCertificate 12868 world12868 agent12868 where
  dimensionLo := 12868
  dimensionHi := 12868
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2239240599 / 1000000000000 : ℝ)
  frameLo := (155832984661 / 250000000000 : ℝ)
  frameHi := (1469535488591 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12868]
  agentFrame_pos := by norm_num only [agent12868]
  worldRadius := (2239240599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12868]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (31559877 / 25000000000 : ℝ)
  lowerTail := (753282553 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3775303501 / 500000000000 : ℝ)
  ledger := by
    have h : (145608411 / 125000000000 : ℚ) +
        (9113975269 / 1000000000000000000 : ℚ) / (2239240599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (31559877 / 25000000000 : ℚ) + (753282553 / 500000000000 : ℚ) ≤
        (3775303501 / 500000000000 : ℚ) := by norm_num only
    have hc : (((145608411 / 125000000000 : ℚ) +
        (9113975269 / 1000000000000000000 : ℚ) / (2239240599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (31559877 / 25000000000 : ℚ) + (753282553 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3775303501 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12868]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12868 :
    2 * 160 < 12868 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997411 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12868 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12869 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12869. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12869 : WorldParameters where
  hiddenCharge := (1164825571 / 1000000000000 : ℝ)
  frame := (623318461709 / 1000000000000 : ℝ)
  moment := (1822425083 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12869 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (91844069393 / 62500000000 : ℝ)
    root := (1047885419 / 125000000000 : ℝ) }

noncomputable def scalar12869 : ScalarCertificate 12869 world12869 agent12869 where
  dimensionLo := 12869
  dimensionHi := 12869
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2239600499 / 1000000000000 : ℝ)
  frameLo := (623318461709 / 1000000000000 : ℝ)
  frameHi := (91844069393 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12869]
  agentFrame_pos := by norm_num only [agent12869]
  worldRadius := (2239600499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12869]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1261347221 / 1000000000000 : ℝ)
  lowerTail := (150540403 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1886850853 / 250000000000 : ℝ)
  ledger := by
    have h : (1164825571 / 1000000000000 : ℚ) +
        (1822425083 / 200000000000000000 : ℚ) / (2239600499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1261347221 / 1000000000000 : ℚ) + (150540403 / 100000000000 : ℚ) ≤
        (1886850853 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1164825571 / 1000000000000 : ℚ) +
        (1822425083 / 200000000000000000 : ℚ) / (2239600499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1261347221 / 1000000000000 : ℚ) + (150540403 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1886850853 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12869]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12869 :
    2 * 160 < 12869 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1249999791 / 125000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12869 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12870 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12870. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12870 : WorldParameters where
  hiddenCharge := (232956773 / 200000000000 : ℝ)
  frame := (311652493451 / 500000000000 : ℝ)
  moment := (1822055217 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12870 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1469395319443 / 1000000000000 : ℝ)
    root := (2095608727 / 250000000000 : ℝ) }

noncomputable def scalar12870 : ScalarCertificate 12870 world12870 agent12870 where
  dimensionLo := 12870
  dimensionHi := 12870
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2240075099 / 1000000000000 : ℝ)
  frameLo := (311652493451 / 500000000000 : ℝ)
  frameHi := (1469395319443 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12870]
  agentFrame_pos := by norm_num only [agent12870]
  worldRadius := (2240075099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12870]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (315018889 / 250000000000 : ℝ)
  lowerTail := (1503951377 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7543499133 / 1000000000000 : ℝ)
  ledger := by
    have h : (232956773 / 200000000000 : ℚ) +
        (1822055217 / 200000000000000000 : ℚ) / (2240075099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (315018889 / 250000000000 : ℚ) + (1503951377 / 1000000000000 : ℚ) ≤
        (7543499133 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((232956773 / 200000000000 : ℚ) +
        (1822055217 / 200000000000000000 : ℚ) / (2240075099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (315018889 / 250000000000 : ℚ) + (1503951377 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7543499133 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12870]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12870 :
    2 * 160 < 12870 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996231 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12870 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12871 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12871. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12871 : WorldParameters where
  hiddenCharge := (1164742169 / 1000000000000 : ℝ)
  frame := (311645757111 / 500000000000 : ℝ)
  moment := (113855341 / 12500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12871 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (29387299473 / 20000000000 : ℝ)
    root := (1676357331 / 200000000000 : ℝ) }

noncomputable def scalar12871 : ScalarCertificate 12871 world12871 agent12871 where
  dimensionLo := 12871
  dimensionHi := 12871
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2240435099 / 1000000000000 : ℝ)
  frameLo := (311645757111 / 500000000000 : ℝ)
  frameHi := (29387299473 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12871]
  agentFrame_pos := by norm_num only [agent12871]
  worldRadius := (2240435099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12871]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (314757497 / 250000000000 : ℝ)
  lowerTail := (1502792723 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7540301487 / 1000000000000 : ℝ)
  ledger := by
    have h : (1164742169 / 1000000000000 : ℚ) +
        (113855341 / 12500000000000000 : ℚ) / (2240435099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (314757497 / 250000000000 : ℚ) + (1502792723 / 1000000000000 : ℚ) ≤
        (7540301487 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1164742169 / 1000000000000 : ℚ) +
        (113855341 / 12500000000000000 : ℚ) / (2240435099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (314757497 / 250000000000 : ℚ) + (1502792723 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7540301487 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12871]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12871 :
    2 * 160 < 12871 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996743 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12871 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12872 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12872. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12872 : WorldParameters where
  hiddenCharge := (232940097 / 200000000000 : ℝ)
  frame := (623278043669 / 1000000000000 : ℝ)
  moment := (9106579 / 1000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12872 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1469334640703 / 1000000000000 : ℝ)
    root := (261910581 / 31250000000 : ℝ) }

noncomputable def scalar12872 : ScalarCertificate 12872 world12872 agent12872 where
  dimensionLo := 12872
  dimensionHi := 12872
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2240794999 / 1000000000000 : ℝ)
  frameLo := (623278043669 / 1000000000000 : ℝ)
  frameHi := (1469334640703 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12872]
  agentFrame_pos := by norm_num only [agent12872]
  worldRadius := (2240794999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12872]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (157248167 / 125000000000 : ℝ)
  lowerTail := (1501635017 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (15074213 / 2000000000 : ℝ)
  ledger := by
    have h : (232940097 / 200000000000 : ℚ) +
        (9106579 / 1000000000000000 : ℚ) / (2240794999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (157248167 / 125000000000 : ℚ) + (1501635017 / 1000000000000 : ℚ) ≤
        (15074213 / 2000000000 : ℚ) := by norm_num only
    have hc : (((232940097 / 200000000000 : ℚ) +
        (9106579 / 1000000000000000 : ℚ) / (2240794999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (157248167 / 125000000000 : ℚ) + (1501635017 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((15074213 / 2000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12872]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12872 :
    2 * 160 < 12872 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999847 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12872 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12873 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12873. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12873 : WorldParameters where
  hiddenCharge := (1164658811 / 1000000000000 : ℝ)
  frame := (311632287621 / 500000000000 : ℝ)
  moment := (9104731243 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12873 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1469304326481 / 1000000000000 : ℝ)
    root := (8380490719 / 1000000000000 : ℝ) }

noncomputable def scalar12873 : ScalarCertificate 12873 world12873 agent12873 where
  dimensionLo := 12873
  dimensionHi := 12873
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2241154899 / 1000000000000 : ℝ)
  frameLo := (311632287621 / 500000000000 : ℝ)
  frameHi := (1469304326481 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12873]
  agentFrame_pos := by norm_num only [agent12873]
  worldRadius := (2241154899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12873]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1256941697 / 1000000000000 : ℝ)
  lowerTail := (1500478373 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7533914221 / 1000000000000 : ℝ)
  ledger := by
    have h : (1164658811 / 1000000000000 : ℚ) +
        (9104731243 / 1000000000000000000 : ℚ) / (2241154899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1256941697 / 1000000000000 : ℚ) + (1500478373 / 1000000000000 : ℚ) ≤
        (7533914221 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1164658811 / 1000000000000 : ℚ) +
        (9104731243 / 1000000000000000000 : ℚ) / (2241154899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1256941697 / 1000000000000 : ℚ) + (1500478373 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7533914221 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12873]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12873 :
    2 * 160 < 12873 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (79999999 / 8000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12873 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12874 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12874. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12874 : WorldParameters where
  hiddenCharge := (1164617149 / 1000000000000 : ℝ)
  frame := (623251108941 / 1000000000000 : ℝ)
  moment := (910288401 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12874 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58770961239 / 40000000000 : ℝ)
    root := (2094960743 / 250000000000 : ℝ) }

noncomputable def scalar12874 : ScalarCertificate 12874 world12874 agent12874 where
  dimensionLo := 12874
  dimensionHi := 12874
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2241514999 / 1000000000000 : ℝ)
  frameLo := (623251108941 / 1000000000000 : ℝ)
  frameHi := (58770961239 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12874]
  agentFrame_pos := by norm_num only [agent12874]
  worldRadius := (2241514999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12874]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (50235967 / 40000000000 : ℝ)
  lowerTail := (1499322909 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7530724549 / 1000000000000 : ℝ)
  ledger := by
    have h : (1164617149 / 1000000000000 : ℚ) +
        (910288401 / 100000000000000000 : ℚ) / (2241514999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (50235967 / 40000000000 : ℚ) + (1499322909 / 1000000000000 : ℚ) ≤
        (7530724549 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1164617149 / 1000000000000 : ℚ) +
        (910288401 / 100000000000000000 : ℚ) / (2241514999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (50235967 / 40000000000 : ℚ) + (1499322909 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7530724549 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12874]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12874 :
    2 * 160 < 12874 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999361 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12874 {← IO.monoMsNow}" : IO Unit)
