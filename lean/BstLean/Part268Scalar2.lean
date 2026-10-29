import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12400 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12400. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12400 : WorldParameters where
  hiddenCharge := (1185653601 / 1000000000000 : ℝ)
  frame := (25195291021 / 40000000000 : ℝ)
  moment := (10040747007 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12400 : AgentParameters :=
  { agentLedgerParameters with
    charge := (452837959 / 250000000000 : ℝ)
    frame := (744373460873 / 500000000000 : ℝ)
    root := (8708753839 / 1000000000000 : ℝ) }

noncomputable def scalar12400 : ScalarCertificate 12400 world12400 agent12400 where
  dimensionLo := 12400
  dimensionHi := 12400
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2067813699 / 1000000000000 : ℝ)
  frameLo := (25195291021 / 40000000000 : ℝ)
  frameHi := (744373460873 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12400]
  agentFrame_pos := by norm_num only [agent12400]
  worldRadius := (2067813699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12400]
  retainedCharge := (452837959 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (948747737 / 500000000000 : ℝ)
  lowerTail := (88108379 / 40000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2361363827 / 250000000000 : ℝ)
  ledger := by
    have h : (1185653601 / 1000000000000 : ℚ) +
        (10040747007 / 1000000000000000000 : ℚ) / (2067813699 / 1000000000000 : ℚ) ^ 2 +
        (452837959 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (948747737 / 500000000000 : ℚ) + (88108379 / 40000000000 : ℚ) ≤
        (2361363827 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1185653601 / 1000000000000 : ℚ) +
        (10040747007 / 1000000000000000000 : ℚ) / (2067813699 / 1000000000000 : ℚ) ^ 2 +
        (452837959 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (948747737 / 500000000000 : ℚ) + (88108379 / 40000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2361363827 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12400]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12400 :
    2 * 160 < 12400 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998099 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12400 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12401 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12401. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12401 : WorldParameters where
  hiddenCharge := (1185606349 / 1000000000000 : ℝ)
  frame := (78733467571 / 125000000000 : ℝ)
  moment := (2007725823 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12401 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1810678739 / 1000000000000 : ℝ)
    frame := (148871111931 / 100000000000 : ℝ)
    root := (8708011801 / 1000000000000 : ℝ) }

noncomputable def scalar12401 : ScalarCertificate 12401 world12401 agent12401 where
  dimensionLo := 12401
  dimensionHi := 12401
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2068163999 / 1000000000000 : ℝ)
  frameLo := (78733467571 / 125000000000 : ℝ)
  frameHi := (148871111931 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12401]
  agentFrame_pos := by norm_num only [agent12401]
  worldRadius := (2068163999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12401]
  retainedCharge := (1810678739 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (473958767 / 250000000000 : ℝ)
  lowerTail := (220091823 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9439992751 / 1000000000000 : ℝ)
  ledger := by
    have h : (1185606349 / 1000000000000 : ℚ) +
        (2007725823 / 200000000000000000 : ℚ) / (2068163999 / 1000000000000 : ℚ) ^ 2 +
        (1810678739 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (473958767 / 250000000000 : ℚ) + (220091823 / 100000000000 : ℚ) ≤
        (9439992751 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1185606349 / 1000000000000 : ℚ) +
        (2007725823 / 200000000000000000 : ℚ) / (2068163999 / 1000000000000 : ℚ) ^ 2 +
        (1810678739 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (473958767 / 250000000000 : ℚ) + (220091823 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9439992751 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12401]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12401 :
    2 * 160 < 12401 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999909 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12401 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12402 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12402. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12402 : WorldParameters where
  hiddenCharge := (118555911 / 100000000000 : ℝ)
  frame := (157463302003 / 250000000000 : ℝ)
  moment := (10036511847 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12402 : AgentParameters :=
  { agentLedgerParameters with
    charge := (905003121 / 500000000000 : ℝ)
    frame := (744337670213 / 500000000000 : ℝ)
    root := (1741454001 / 200000000000 : ℝ) }

noncomputable def scalar12402 : ScalarCertificate 12402 world12402 agent12402 where
  dimensionLo := 12402
  dimensionHi := 12402
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2068514299 / 1000000000000 : ℝ)
  frameLo := (157463302003 / 250000000000 : ℝ)
  frameHi := (744337670213 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12402]
  agentFrame_pos := by norm_num only [agent12402]
  worldRadius := (2068514299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12402]
  retainedCharge := (905003121 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (947088183 / 500000000000 : ℝ)
  lowerTail := (2199128723 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9434535133 / 1000000000000 : ℝ)
  ledger := by
    have h : (118555911 / 100000000000 : ℚ) +
        (10036511847 / 1000000000000000000 : ℚ) / (2068514299 / 1000000000000 : ℚ) ^ 2 +
        (905003121 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (947088183 / 500000000000 : ℚ) + (2199128723 / 1000000000000 : ℚ) ≤
        (9434535133 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((118555911 / 100000000000 : ℚ) +
        (10036511847 / 1000000000000000000 : ℚ) / (2068514299 / 1000000000000 : ℚ) ^ 2 +
        (905003121 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (947088183 / 500000000000 : ℚ) + (2199128723 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9434535133 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12402]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12402 :
    2 * 160 < 12402 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999131 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12402 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12403 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12403. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12403 : WorldParameters where
  hiddenCharge := (296377971 / 250000000000 : ℝ)
  frame := (19682458683 / 31250000000 : ℝ)
  moment := (10034395203 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12403 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1809334343 / 1000000000000 : ℝ)
    frame := (1488639585081 / 1000000000000 : ℝ)
    root := (8706528451 / 1000000000000 : ℝ) }

noncomputable def scalar12403 : ScalarCertificate 12403 world12403 agent12403 where
  dimensionLo := 12403
  dimensionHi := 12403
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2068864399 / 1000000000000 : ℝ)
  frameLo := (19682458683 / 31250000000 : ℝ)
  frameHi := (1488639585081 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12403]
  agentFrame_pos := by norm_num only [agent12403]
  worldRadius := (2068864399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12403]
  retainedCharge := (1809334343 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (473129787 / 250000000000 : ℝ)
  lowerTail := (2197340717 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (188581649 / 20000000000 : ℝ)
  ledger := by
    have h : (296377971 / 250000000000 : ℚ) +
        (10034395203 / 1000000000000000000 : ℚ) / (2068864399 / 1000000000000 : ℚ) ^ 2 +
        (1809334343 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (473129787 / 250000000000 : ℚ) + (2197340717 / 1000000000000 : ℚ) ≤
        (188581649 / 20000000000 : ℚ) := by norm_num only
    have hc : (((296377971 / 250000000000 : ℚ) +
        (10034395203 / 1000000000000000000 : ℚ) / (2068864399 / 1000000000000 : ℚ) ^ 2 +
        (1809334343 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (473129787 / 250000000000 : ℚ) + (2197340717 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((188581649 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12403]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12403 :
    2 * 160 < 12403 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995043 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12403 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12404 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12404. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12404 : WorldParameters where
  hiddenCharge := (1185464671 / 1000000000000 : ℝ)
  frame := (629824150099 / 1000000000000 : ℝ)
  moment := (5016139591 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12404 : AgentParameters :=
  { agentLedgerParameters with
    charge := (452165761 / 250000000000 : ℝ)
    frame := (1488603847271 / 1000000000000 : ℝ)
    root := (4352893569 / 500000000000 : ℝ) }

noncomputable def scalar12404 : ScalarCertificate 12404 world12404 agent12404 where
  dimensionLo := 12404
  dimensionHi := 12404
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2069214699 / 1000000000000 : ℝ)
  frameLo := (629824150099 / 1000000000000 : ℝ)
  frameHi := (1488603847271 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12404]
  agentFrame_pos := by norm_num only [agent12404]
  worldRadius := (2069214699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12404]
  retainedCharge := (452165761 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (378172763 / 200000000000 : ℝ)
  lowerTail := (2195554639 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4711817311 / 500000000000 : ℝ)
  ledger := by
    have h : (1185464671 / 1000000000000 : ℚ) +
        (5016139591 / 500000000000000000 : ℚ) / (2069214699 / 1000000000000 : ℚ) ^ 2 +
        (452165761 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (378172763 / 200000000000 : ℚ) + (2195554639 / 1000000000000 : ℚ) ≤
        (4711817311 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1185464671 / 1000000000000 : ℚ) +
        (5016139591 / 500000000000000000 : ℚ) / (2069214699 / 1000000000000 : ℚ) ^ 2 +
        (452165761 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (378172763 / 200000000000 : ℚ) + (2195554639 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4711817311 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12404]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12404 :
    2 * 160 < 12404 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (549999783 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12404 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12405 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12405. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12405 : WorldParameters where
  hiddenCharge := (118541747 / 100000000000 : ℝ)
  frame := (31490481237 / 50000000000 : ℝ)
  moment := (2006032757 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12405 : AgentParameters :=
  { agentLedgerParameters with
    charge := (903996171 / 500000000000 : ℝ)
    frame := (372142033243 / 250000000000 : ℝ)
    root := (8705046067 / 1000000000000 : ℝ) }

noncomputable def scalar12405 : ScalarCertificate 12405 world12405 agent12405 where
  dimensionLo := 12405
  dimensionHi := 12405
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2069564999 / 1000000000000 : ℝ)
  frameLo := (31490481237 / 50000000000 : ℝ)
  frameHi := (372142033243 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12405]
  agentFrame_pos := by norm_num only [agent12405]
  worldRadius := (2069564999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12405]
  retainedCharge := (903996171 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1889210181 / 1000000000000 : ℝ)
  lowerTail := (1096885147 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9418191719 / 1000000000000 : ℝ)
  ledger := by
    have h : (118541747 / 100000000000 : ℚ) +
        (2006032757 / 200000000000000000 : ℚ) / (2069564999 / 1000000000000 : ℚ) ^ 2 +
        (903996171 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1889210181 / 1000000000000 : ℚ) + (1096885147 / 500000000000 : ℚ) ≤
        (9418191719 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((118541747 / 100000000000 : ℚ) +
        (2006032757 / 200000000000000000 : ℚ) / (2069564999 / 1000000000000 : ℚ) ^ 2 +
        (903996171 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1889210181 / 1000000000000 : ℚ) + (1096885147 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9418191719 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12405]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12405 :
    2 * 160 < 12405 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994017 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12405 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12406 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12406. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12406 : WorldParameters where
  hiddenCharge := (592685141 / 500000000000 : ℝ)
  frame := (31489755089 / 50000000000 : ℝ)
  moment := (2507012253 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12406 : AgentParameters :=
  { agentLedgerParameters with
    charge := (451830559 / 250000000000 : ℝ)
    frame := (1488532436181 / 1000000000000 : ℝ)
    root := (2176076309 / 250000000000 : ℝ) }

noncomputable def scalar12406 : ScalarCertificate 12406 world12406 agent12406 where
  dimensionLo := 12406
  dimensionHi := 12406
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2069915299 / 1000000000000 : ℝ)
  frameLo := (31489755089 / 50000000000 : ℝ)
  frameHi := (1488532436181 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12406]
  agentFrame_pos := by norm_num only [agent12406]
  worldRadius := (2069915299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12406]
  retainedCharge := (451830559 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (188755821 / 100000000000 : ℝ)
  lowerTail := (2191987639 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9412753661 / 1000000000000 : ℝ)
  ledger := by
    have h : (592685141 / 500000000000 : ℚ) +
        (2507012253 / 250000000000000000 : ℚ) / (2069915299 / 1000000000000 : ℚ) ^ 2 +
        (451830559 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (188755821 / 100000000000 : ℚ) + (2191987639 / 1000000000000 : ℚ) ≤
        (9412753661 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((592685141 / 500000000000 : ℚ) +
        (2507012253 / 250000000000000000 : ℚ) / (2069915299 / 1000000000000 : ℚ) ^ 2 +
        (451830559 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (188755821 / 100000000000 : ℚ) + (2191987639 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9412753661 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12406]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12406 :
    2 * 160 < 12406 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998083 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12406 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12407 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12407. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12407 : WorldParameters where
  hiddenCharge := (1185323107 / 1000000000000 : ℝ)
  frame := (629780581217 / 1000000000000 : ℝ)
  moment := (10025934861 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12407 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1806652727 / 1000000000000 : ℝ)
    frame := (186062095359 / 125000000000 : ℝ)
    root := (8703564647 / 1000000000000 : ℝ) }

noncomputable def scalar12407 : ScalarCertificate 12407 world12407 agent12407 where
  dimensionLo := 12407
  dimensionHi := 12407
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2070265599 / 1000000000000 : ℝ)
  frameLo := (629780581217 / 1000000000000 : ℝ)
  frameHi := (186062095359 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12407]
  agentFrame_pos := by norm_num only [agent12407]
  worldRadius := (2070265599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12407]
  retainedCharge := (1806652727 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1885907933 / 1000000000000 : ℝ)
  lowerTail := (273775839 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2351830129 / 250000000000 : ℝ)
  ledger := by
    have h : (1185323107 / 1000000000000 : ℚ) +
        (10025934861 / 1000000000000000000 : ℚ) / (2070265599 / 1000000000000 : ℚ) ^ 2 +
        (1806652727 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1885907933 / 1000000000000 : ℚ) + (273775839 / 125000000000 : ℚ) ≤
        (2351830129 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1185323107 / 1000000000000 : ℚ) +
        (10025934861 / 1000000000000000000 : ℚ) / (2070265599 / 1000000000000 : ℚ) ^ 2 +
        (1806652727 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1885907933 / 1000000000000 : ℚ) + (273775839 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2351830129 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12407]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12407 :
    2 * 160 < 12407 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999001 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12407 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12408 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12408. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12408 : WorldParameters where
  hiddenCharge := (237055189 / 200000000000 : ℝ)
  frame := (12595321261 / 20000000000 : ℝ)
  moment := (10023821333 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12408 : AgentParameters :=
  { agentLedgerParameters with
    charge := (361196763 / 200000000000 : ℝ)
    frame := (297692221409 / 200000000000 : ℝ)
    root := (2175706057 / 250000000000 : ℝ) }

noncomputable def scalar12408 : ScalarCertificate 12408 world12408 agent12408 where
  dimensionLo := 12408
  dimensionHi := 12408
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2070615799 / 1000000000000 : ℝ)
  frameLo := (12595321261 / 20000000000 : ℝ)
  frameHi := (297692221409 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12408]
  agentFrame_pos := by norm_num only [agent12408]
  worldRadius := (2070615799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12408]
  retainedCharge := (361196763 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (188425913 / 100000000000 : ℝ)
  lowerTail := (2188427279 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1880378411 / 200000000000 : ℝ)
  ledger := by
    have h : (237055189 / 200000000000 : ℚ) +
        (10023821333 / 1000000000000000000 : ℚ) / (2070615799 / 1000000000000 : ℚ) ^ 2 +
        (361196763 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (188425913 / 100000000000 : ℚ) + (2188427279 / 1000000000000 : ℚ) ≤
        (1880378411 / 200000000000 : ℚ) := by norm_num only
    have hc : (((237055189 / 200000000000 : ℚ) +
        (10023821333 / 1000000000000000000 : ℚ) / (2070615799 / 1000000000000 : ℚ) ^ 2 +
        (361196763 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (188425913 / 100000000000 : ℚ) + (2188427279 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1880378411 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12408]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12408 :
    2 * 160 < 12408 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999897 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12408 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12409 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12409. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12409 : WorldParameters where
  hiddenCharge := (296307199 / 250000000000 : ℝ)
  frame := (7871894341 / 12500000000 : ℝ)
  moment := (10021708427 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12409 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1805315497 / 1000000000000 : ℝ)
    frame := (186053173857 / 125000000000 : ℝ)
    root := (217552103 / 25000000000 : ℝ) }

noncomputable def scalar12409 : ScalarCertificate 12409 world12409 agent12409 where
  dimensionLo := 12409
  dimensionHi := 12409
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2070966199 / 1000000000000 : ℝ)
  frameLo := (7871894341 / 12500000000 : ℝ)
  frameHi := (186053173857 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12409]
  agentFrame_pos := by norm_num only [agent12409]
  worldRadius := (2070966199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12409]
  retainedCharge := (1805315497 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1882611853 / 1000000000000 : ℝ)
  lowerTail := (1093324661 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (587279227 / 62500000000 : ℝ)
  ledger := by
    have h : (296307199 / 250000000000 : ℚ) +
        (10021708427 / 1000000000000000000 : ℚ) / (2070966199 / 1000000000000 : ℚ) ^ 2 +
        (1805315497 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1882611853 / 1000000000000 : ℚ) + (1093324661 / 500000000000 : ℚ) ≤
        (587279227 / 62500000000 : ℚ) := by norm_num only
    have hc : (((296307199 / 250000000000 : ℚ) +
        (10021708427 / 1000000000000000000 : ℚ) / (2070966199 / 1000000000000 : ℚ) ^ 2 +
        (1805315497 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1882611853 / 1000000000000 : ℚ) + (1093324661 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((587279227 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12409]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12409 :
    2 * 160 < 12409 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997251 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12409 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12410 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12410. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12410 : WorldParameters where
  hiddenCharge := (1185181659 / 1000000000000 : ℝ)
  frame := (125947406781 / 200000000000 : ℝ)
  moment := (626224759 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12410 : AgentParameters :=
  { agentLedgerParameters with
    charge := (902323887 / 500000000000 : ℝ)
    frame := (23254758919 / 15625000000 : ℝ)
    root := (8701344253 / 1000000000000 : ℝ) }

noncomputable def scalar12410 : ScalarCertificate 12410 world12410 agent12410 where
  dimensionLo := 12410
  dimensionHi := 12410
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2071425099 / 1000000000000 : ℝ)
  frameLo := (125947406781 / 200000000000 : ℝ)
  frameHi := (23254758919 / 15625000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12410]
  agentFrame_pos := by norm_num only [agent12410]
  worldRadius := (2071425099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12410]
  retainedCharge := (902323887 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1880618953 / 1000000000000 : ℝ)
  lowerTail := (2184434427 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (939001749 / 100000000000 : ℝ)
  ledger := by
    have h : (1185181659 / 1000000000000 : ℚ) +
        (626224759 / 62500000000000000 : ℚ) / (2071425099 / 1000000000000 : ℚ) ^ 2 +
        (902323887 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1880618953 / 1000000000000 : ℚ) + (2184434427 / 1000000000000 : ℚ) ≤
        (939001749 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1185181659 / 1000000000000 : ℚ) +
        (626224759 / 62500000000000000 : ℚ) / (2071425099 / 1000000000000 : ℚ) ^ 2 +
        (902323887 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1880618953 / 1000000000000 : ℚ) + (2184434427 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((939001749 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12410]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12410 :
    2 * 160 < 12410 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999991 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12410 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12411 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12411. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12411 : WorldParameters where
  hiddenCharge := (237026907 / 200000000000 : ℝ)
  frame := (25188900917 / 40000000000 : ℝ)
  moment := (10017484483 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12411 : AgentParameters :=
  { agentLedgerParameters with
    charge := (360796129 / 200000000000 : ℝ)
    frame := (74413432557 / 50000000000 : ℝ)
    root := (4350302313 / 500000000000 : ℝ) }

noncomputable def scalar12411 : ScalarCertificate 12411 world12411 agent12411 where
  dimensionLo := 12411
  dimensionHi := 12411
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2071775799 / 1000000000000 : ℝ)
  frameLo := (25188900917 / 40000000000 : ℝ)
  frameHi := (74413432557 / 50000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12411]
  agentFrame_pos := by norm_num only [agent12411]
  worldRadius := (2071775799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12411]
  retainedCharge := (360796129 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (469743563 / 250000000000 : ℝ)
  lowerTail := (1091329443 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2346150133 / 250000000000 : ℝ)
  ledger := by
    have h : (237026907 / 200000000000 : ℚ) +
        (10017484483 / 1000000000000000000 : ℚ) / (2071775799 / 1000000000000 : ℚ) ^ 2 +
        (360796129 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (469743563 / 250000000000 : ℚ) + (1091329443 / 500000000000 : ℚ) ≤
        (2346150133 / 250000000000 : ℚ) := by norm_num only
    have hc : (((237026907 / 200000000000 : ℚ) +
        (10017484483 / 1000000000000000000 : ℚ) / (2071775799 / 1000000000000 : ℚ) ^ 2 +
        (360796129 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (469743563 / 250000000000 : ℚ) + (1091329443 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2346150133 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12411]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12411 :
    2 * 160 < 12411 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (54999977 / 5000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12411 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12412 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12412. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12412 : WorldParameters where
  hiddenCharge := (18516991 / 15625000000 : ℝ)
  frame := (629708014339 / 1000000000000 : ℝ)
  moment := (10015373443 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12412 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1803314109 / 1000000000000 : ℝ)
    frame := (297646549783 / 200000000000 : ℝ)
    root := (217496631 / 25000000000 : ℝ) }

noncomputable def scalar12412 : ScalarCertificate 12412 world12412 agent12412 where
  dimensionLo := 12412
  dimensionHi := 12412
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2072126599 / 1000000000000 : ℝ)
  frameLo := (629708014339 / 1000000000000 : ℝ)
  frameHi := (297646549783 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12412]
  agentFrame_pos := by norm_num only [agent12412]
  worldRadius := (2072126599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12412]
  retainedCharge := (1803314109 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1877331313 / 1000000000000 : ℝ)
  lowerTail := (1090442571 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4689594197 / 500000000000 : ℝ)
  ledger := by
    have h : (18516991 / 15625000000 : ℚ) +
        (10015373443 / 1000000000000000000 : ℚ) / (2072126599 / 1000000000000 : ℚ) ^ 2 +
        (1803314109 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1877331313 / 1000000000000 : ℚ) + (1090442571 / 500000000000 : ℚ) ≤
        (4689594197 / 500000000000 : ℚ) := by norm_num only
    have hc : (((18516991 / 15625000000 : ℚ) +
        (10015373443 / 1000000000000000000 : ℚ) / (2072126599 / 1000000000000 : ℚ) ^ 2 +
        (1803314109 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1877331313 / 1000000000000 : ℚ) + (1090442571 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4689594197 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12412]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12412 :
    2 * 160 < 12412 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995493 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12412 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12413 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12413. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12413 : WorldParameters where
  hiddenCharge := (592520163 / 500000000000 : ℝ)
  frame := (629693508147 / 1000000000000 : ℝ)
  moment := (400530521 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12413 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1802648167 / 1000000000000 : ℝ)
    frame := (1488196870113 / 1000000000000 : ℝ)
    root := (8699126093 / 1000000000000 : ℝ) }

noncomputable def scalar12413 : ScalarCertificate 12413 world12413 agent12413 where
  dimensionLo := 12413
  dimensionHi := 12413
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2072477299 / 1000000000000 : ℝ)
  frameLo := (629693508147 / 1000000000000 : ℝ)
  frameHi := (1488196870113 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12413]
  agentFrame_pos := by norm_num only [agent12413]
  worldRadius := (2072477299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12413]
  retainedCharge := (1802648167 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1875689949 / 1000000000000 : ℝ)
  lowerTail := (2179113 / 1000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4686890571 / 500000000000 : ℝ)
  ledger := by
    have h : (592520163 / 500000000000 : ℚ) +
        (400530521 / 40000000000000000 : ℚ) / (2072477299 / 1000000000000 : ℚ) ^ 2 +
        (1802648167 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1875689949 / 1000000000000 : ℚ) + (2179113 / 1000000000 : ℚ) ≤
        (4686890571 / 500000000000 : ℚ) := by norm_num only
    have hc : (((592520163 / 500000000000 : ℚ) +
        (400530521 / 40000000000000000 : ℚ) / (2072477299 / 1000000000000 : ℚ) ^ 2 +
        (1802648167 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1875689949 / 1000000000000 : ℚ) + (2179113 / 1000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4686890571 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12413]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12413 :
    2 * 160 < 12413 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997113 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12413 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12414 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12414. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12414 : WorldParameters where
  hiddenCharge := (1184993241 / 1000000000000 : ℝ)
  frame := (157419751087 / 250000000000 : ℝ)
  moment := (2502788307 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12414 : AgentParameters :=
  { agentLedgerParameters with
    charge := (56311963 / 31250000000 : ℝ)
    frame := (744080504367 / 500000000000 : ℝ)
    root := (8698387187 / 1000000000000 : ℝ) }

noncomputable def scalar12414 : ScalarCertificate 12414 world12414 agent12414 where
  dimensionLo := 12414
  dimensionHi := 12414
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2072828099 / 1000000000000 : ℝ)
  frameLo := (157419751087 / 250000000000 : ℝ)
  frameHi := (744080504367 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12414]
  agentFrame_pos := by norm_num only [agent12414]
  worldRadius := (2072828099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12414]
  retainedCharge := (56311963 / 31250000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1874050343 / 1000000000000 : ℝ)
  lowerTail := (544335663 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9368378699 / 1000000000000 : ℝ)
  ledger := by
    have h : (1184993241 / 1000000000000 : ℚ) +
        (2502788307 / 250000000000000000 : ℚ) / (2072828099 / 1000000000000 : ℚ) ^ 2 +
        (56311963 / 31250000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1874050343 / 1000000000000 : ℚ) + (544335663 / 250000000000 : ℚ) ≤
        (9368378699 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1184993241 / 1000000000000 : ℚ) +
        (2502788307 / 250000000000000000 : ℚ) / (2072828099 / 1000000000000 : ℚ) ^ 2 +
        (56311963 / 31250000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1874050343 / 1000000000000 : ℚ) + (544335663 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9368378699 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12414]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12414 :
    2 * 160 < 12414 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (687499849 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12414 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12415 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12415. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12415 : WorldParameters where
  hiddenCharge := (148118271 / 125000000000 : ℝ)
  frame := (629664502941 / 1000000000000 : ℝ)
  moment := (10009044053 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12415 : AgentParameters :=
  { agentLedgerParameters with
    charge := (900659029 / 500000000000 : ℝ)
    frame := (1488125170749 / 1000000000000 : ℝ)
    root := (217441213 / 25000000000 : ℝ) }

noncomputable def scalar12415 : ScalarCertificate 12415 world12415 agent12415 where
  dimensionLo := 12415
  dimensionHi := 12415
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2073178799 / 1000000000000 : ℝ)
  frameLo := (629664502941 / 1000000000000 : ℝ)
  frameHi := (1488125170749 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12415]
  agentFrame_pos := by norm_num only [agent12415]
  worldRadius := (2073178799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12415]
  retainedCharge := (900659029 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (468103077 / 250000000000 : ℝ)
  lowerTail := (1087786951 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9362981133 / 1000000000000 : ℝ)
  ledger := by
    have h : (148118271 / 125000000000 : ℚ) +
        (10009044053 / 1000000000000000000 : ℚ) / (2073178799 / 1000000000000 : ℚ) ^ 2 +
        (900659029 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (468103077 / 250000000000 : ℚ) + (1087786951 / 500000000000 : ℚ) ≤
        (9362981133 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((148118271 / 125000000000 : ℚ) +
        (10009044053 / 1000000000000000000 : ℚ) / (2073178799 / 1000000000000 : ℚ) ^ 2 +
        (900659029 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (468103077 / 250000000000 : ℚ) + (1087786951 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9362981133 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12415]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12415 :
    2 * 160 < 12415 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999763 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12415 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12416 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12416. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12416 : WorldParameters where
  hiddenCharge := (296224777 / 250000000000 : ℝ)
  frame := (314825001963 / 500000000000 : ℝ)
  moment := (5003467749 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12416 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1800653891 / 1000000000000 : ℝ)
    frame := (1488089362131 / 1000000000000 : ℝ)
    root := (8696910093 / 1000000000000 : ℝ) }

noncomputable def scalar12416 : ScalarCertificate 12416 world12416 agent12416 where
  dimensionLo := 12416
  dimensionHi := 12416
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2073529599 / 1000000000000 : ℝ)
  frameLo := (314825001963 / 500000000000 : ℝ)
  frameHi := (1488089362131 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12416]
  agentFrame_pos := by norm_num only [agent12416]
  worldRadius := (2073529599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12416]
  retainedCharge := (1800653891 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1870776093 / 1000000000000 : ℝ)
  lowerTail := (108690351 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (935758851 / 100000000000 : ℝ)
  ledger := by
    have h : (296224777 / 250000000000 : ℚ) +
        (5003467749 / 500000000000000000 : ℚ) / (2073529599 / 1000000000000 : ℚ) ^ 2 +
        (1800653891 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1870776093 / 1000000000000 : ℚ) + (108690351 / 50000000000 : ℚ) ≤
        (935758851 / 100000000000 : ℚ) := by norm_num only
    have hc : (((296224777 / 250000000000 : ℚ) +
        (5003467749 / 500000000000000000 : ℚ) / (2073529599 / 1000000000000 : ℚ) ^ 2 +
        (1800653891 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1870776093 / 1000000000000 : ℚ) + (108690351 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((935758851 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12416]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12416 :
    2 * 160 < 12416 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994003 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12416 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12417 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12417. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12417 : WorldParameters where
  hiddenCharge := (1184852061 / 1000000000000 : ℝ)
  frame := (314817753651 / 500000000000 : ℝ)
  moment := (2501206891 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12417 : AgentParameters :=
  { agentLedgerParameters with
    charge := (899995157 / 500000000000 : ℝ)
    frame := (1488053564911 / 1000000000000 : ℝ)
    root := (4348085917 / 500000000000 : ℝ) }

noncomputable def scalar12417 : ScalarCertificate 12417 world12417 agent12417 where
  dimensionLo := 12417
  dimensionHi := 12417
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2073880399 / 1000000000000 : ℝ)
  frameLo := (314817753651 / 500000000000 : ℝ)
  frameHi := (1488053564911 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12417]
  agentFrame_pos := by norm_num only [agent12417]
  worldRadius := (2073880399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12417]
  retainedCharge := (899995157 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (467285353 / 250000000000 : ℝ)
  lowerTail := (67876303 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4676100229 / 500000000000 : ℝ)
  ledger := by
    have h : (1184852061 / 1000000000000 : ℚ) +
        (2501206891 / 250000000000000000 : ℚ) / (2073880399 / 1000000000000 : ℚ) ^ 2 +
        (899995157 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (467285353 / 250000000000 : ℚ) + (67876303 / 31250000000 : ℚ) ≤
        (4676100229 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1184852061 / 1000000000000 : ℚ) +
        (2501206891 / 250000000000000000 : ℚ) / (2073880399 / 1000000000000 : ℚ) ^ 2 +
        (899995157 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (467285353 / 250000000000 : ℚ) + (67876303 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((4676100229 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12417]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12417 :
    2 * 160 < 12417 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999881 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12417 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12418 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12418. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12418 : WorldParameters where
  hiddenCharge := (592402513 / 500000000000 : ℝ)
  frame := (157405253267 / 250000000000 : ℝ)
  moment := (40010881 / 4000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12418 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1799327327 / 1000000000000 : ℝ)
    frame := (372004449257 / 250000000000 : ℝ)
    root := (4347716943 / 500000000000 : ℝ) }

noncomputable def scalar12418 : ScalarCertificate 12418 world12418 agent12418 where
  dimensionLo := 12418
  dimensionHi := 12418
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2074231199 / 1000000000000 : ℝ)
  frameLo := (157405253267 / 250000000000 : ℝ)
  frameHi := (372004449257 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12418]
  agentFrame_pos := by norm_num only [agent12418]
  worldRadius := (2074231199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12418]
  retainedCharge := (1799327327 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (933754257 / 500000000000 : ℝ)
  lowerTail := (1085139097 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9346817489 / 1000000000000 : ℝ)
  ledger := by
    have h : (592402513 / 500000000000 : ℚ) +
        (40010881 / 4000000000000000 : ℚ) / (2074231199 / 1000000000000 : ℚ) ^ 2 +
        (1799327327 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (933754257 / 500000000000 : ℚ) + (1085139097 / 500000000000 : ℚ) ≤
        (9346817489 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((592402513 / 500000000000 : ℚ) +
        (40010881 / 4000000000000000 : ℚ) / (2074231199 / 1000000000000 : ℚ) ^ 2 +
        (1799327327 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (933754257 / 500000000000 : ℚ) + (1085139097 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9346817489 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12418]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12418 :
    2 * 160 < 12418 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996569 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12418 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12419 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12419. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12419 : WorldParameters where
  hiddenCharge := (296189501 / 250000000000 : ℝ)
  frame := (78700815153 / 125000000000 : ℝ)
  moment := (2500153389 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12419 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (2975964093 / 2000000000 : ℝ)
    root := (543418511 / 62500000000 : ℝ) }

noncomputable def scalar12419 : ScalarCertificate 12419 world12419 agent12419 where
  dimensionLo := 12419
  dimensionHi := 12419
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2074581899 / 1000000000000 : ℝ)
  frameLo := (78700815153 / 125000000000 : ℝ)
  frameHi := (2975964093 / 2000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12419]
  agentFrame_pos := by norm_num only [agent12419]
  worldRadius := (2074581899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12419]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1865877147 / 1000000000000 : ℝ)
  lowerTail := (542129061 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (14947071 / 1600000000 : ℝ)
  ledger := by
    have h : (296189501 / 250000000000 : ℚ) +
        (2500153389 / 250000000000000000 : ℚ) / (2074581899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1865877147 / 1000000000000 : ℚ) + (542129061 / 250000000000 : ℚ) ≤
        (14947071 / 1600000000 : ℚ) := by norm_num only
    have hc : (((296189501 / 250000000000 : ℚ) +
        (2500153389 / 250000000000000000 : ℚ) / (2074581899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1865877147 / 1000000000000 : ℚ) + (542129061 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((14947071 / 1600000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12419]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12419 :
    2 * 160 < 12419 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999293 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12419 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12420 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12420. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12420 : WorldParameters where
  hiddenCharge := (236942199 / 200000000000 : ℝ)
  frame := (629592031769 / 1000000000000 : ℝ)
  moment := (4999253741 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12420 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1487861575383 / 1000000000000 : ℝ)
    root := (4346979353 / 500000000000 : ℝ) }

noncomputable def scalar12420 : ScalarCertificate 12420 world12420 agent12420 where
  dimensionLo := 12420
  dimensionHi := 12420
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2075040999 / 1000000000000 : ℝ)
  frameLo := (629592031769 / 1000000000000 : ℝ)
  frameHi := (1487861575383 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12420]
  agentFrame_pos := by norm_num only [agent12420]
  worldRadius := (2075040999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12420]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1863904561 / 1000000000000 : ℝ)
  lowerTail := (1083161311 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9336188949 / 1000000000000 : ℝ)
  ledger := by
    have h : (236942199 / 200000000000 : ℚ) +
        (4999253741 / 500000000000000000 : ℚ) / (2075040999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1863904561 / 1000000000000 : ℚ) + (1083161311 / 500000000000 : ℚ) ≤
        (9336188949 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((236942199 / 200000000000 : ℚ) +
        (4999253741 / 500000000000000000 : ℚ) / (2075040999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1863904561 / 1000000000000 : ℚ) + (1083161311 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9336188949 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12420]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12420 :
    2 * 160 < 12420 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999047 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12420 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12421 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12421. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12421 : WorldParameters where
  hiddenCharge := (1184663999 / 1000000000000 : ℝ)
  frame := (629577544703 / 1000000000000 : ℝ)
  moment := (2499100507 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12421 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1487825872541 / 1000000000000 : ℝ)
    root := (4346610737 / 500000000000 : ℝ) }

noncomputable def scalar12421 : ScalarCertificate 12421 world12421 agent12421 where
  dimensionLo := 12421
  dimensionHi := 12421
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2075391799 / 1000000000000 : ℝ)
  frameLo := (629577544703 / 1000000000000 : ℝ)
  frameHi := (1487825872541 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12421]
  agentFrame_pos := by norm_num only [agent12421]
  worldRadius := (2075391799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12421]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (372455377 / 200000000000 : ℝ)
  lowerTail := (2164564483 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (583217649 / 62500000000 : ℝ)
  ledger := by
    have h : (1184663999 / 1000000000000 : ℚ) +
        (2499100507 / 250000000000000000 : ℚ) / (2075391799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (372455377 / 200000000000 : ℚ) + (2164564483 / 1000000000000 : ℚ) ≤
        (583217649 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1184663999 / 1000000000000 : ℚ) +
        (2499100507 / 250000000000000000 : ℚ) / (2075391799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (372455377 / 200000000000 : ℚ) + (2164564483 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((583217649 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12421]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12421 :
    2 * 160 < 12421 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997923 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12421 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12422 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12422. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12422 : WorldParameters where
  hiddenCharge := (148077127 / 125000000000 : ℝ)
  frame := (25182522401 / 40000000000 : ℝ)
  moment := (9994297193 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12422 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (297558038599 / 200000000000 : ℝ)
    root := (8692484481 / 1000000000000 : ℝ) }

noncomputable def scalar12422 : ScalarCertificate 12422 world12422 agent12422 where
  dimensionLo := 12422
  dimensionHi := 12422
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2075742599 / 1000000000000 : ℝ)
  frameLo := (25182522401 / 40000000000 : ℝ)
  frameHi := (297558038599 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12422]
  agentFrame_pos := by norm_num only [agent12422]
  worldRadius := (2075742599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12422]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (930325437 / 500000000000 : ℝ)
  lowerTail := (540702011 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9326780071 / 1000000000000 : ℝ)
  ledger := by
    have h : (148077127 / 125000000000 : ℚ) +
        (9994297193 / 1000000000000000000 : ℚ) / (2075742599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (930325437 / 500000000000 : ℚ) + (540702011 / 250000000000 : ℚ) ≤
        (9326780071 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((148077127 / 125000000000 : ℚ) +
        (9994297193 / 1000000000000000000 : ℚ) / (2075742599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (930325437 / 500000000000 : ℚ) + (540702011 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9326780071 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12422]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12422 :
    2 * 160 < 12422 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997593 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12422 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12423 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12423. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12423 : WorldParameters where
  hiddenCharge := (236914009 / 200000000000 : ℝ)
  frame := (314774288867 / 500000000000 : ℝ)
  moment := (4996096489 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12423 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (5951018123 / 4000000000 : ℝ)
    root := (1086468457 / 125000000000 : ℝ) }

noncomputable def scalar12423 : ScalarCertificate 12423 world12423 agent12423 where
  dimensionLo := 12423
  dimensionHi := 12423
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2076093399 / 1000000000000 : ℝ)
  frameLo := (314774288867 / 500000000000 : ℝ)
  frameHi := (5951018123 / 4000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12423]
  agentFrame_pos := by norm_num only [agent12423]
  worldRadius := (2076093399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12423]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (92951321 / 50000000000 : ℝ)
  lowerTail := (216105319 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4661040891 / 500000000000 : ℝ)
  ledger := by
    have h : (236914009 / 200000000000 : ℚ) +
        (4996096489 / 500000000000000000 : ℚ) / (2076093399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (92951321 / 50000000000 : ℚ) + (216105319 / 100000000000 : ℚ) ≤
        (4661040891 / 500000000000 : ℚ) := by norm_num only
    have hc : (((236914009 / 200000000000 : ℚ) +
        (4996096489 / 500000000000000000 : ℚ) / (2076093399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (92951321 / 50000000000 : ℚ) + (216105319 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4661040891 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12423]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12423 :
    2 * 160 < 12423 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998421 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12423 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12424 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12424. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12424 : WorldParameters where
  hiddenCharge := (1184523087 / 1000000000000 : ℝ)
  frame := (62953409783 / 100000000000 : ℝ)
  moment := (9990089381 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12424 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (59508755671 / 40000000000 : ℝ)
    root := (434550557 / 50000000000 : ℝ) }

noncomputable def scalar12424 : ScalarCertificate 12424 world12424 agent12424 where
  dimensionLo := 12424
  dimensionHi := 12424
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2076444199 / 1000000000000 : ℝ)
  frameLo := (62953409783 / 100000000000 : ℝ)
  frameHi := (59508755671 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12424]
  agentFrame_pos := by norm_num only [agent12424]
  worldRadius := (2076444199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12424]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1857403703 / 1000000000000 : ℝ)
  lowerTail := (539825027 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4658693943 / 500000000000 : ℝ)
  ledger := by
    have h : (1184523087 / 1000000000000 : ℚ) +
        (9990089381 / 1000000000000000000 : ℚ) / (2076444199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1857403703 / 1000000000000 : ℚ) + (539825027 / 250000000000 : ℚ) ≤
        (4658693943 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1184523087 / 1000000000000 : ℚ) +
        (9990089381 / 1000000000000000000 : ℚ) / (2076444199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1857403703 / 1000000000000 : ℚ) + (539825027 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4658693943 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12424]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12424 :
    2 * 160 < 12424 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996831 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12424 {← IO.monoMsNow}" : IO Unit)
