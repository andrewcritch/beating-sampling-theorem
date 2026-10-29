import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12280 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12280. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12280 : WorldParameters where
  hiddenCharge := (595709131 / 500000000000 : ℝ)
  frame := (631644086867 / 1000000000000 : ℝ)
  moment := (2574873981 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12280 : AgentParameters :=
  { agentLedgerParameters with
    charge := (186927789 / 100000000000 : ℝ)
    frame := (364445406379 / 250000000000 : ℝ)
    root := (8809199889 / 1000000000000 : ℝ) }

noncomputable def scalar12280 : ScalarCertificate 12280 world12280 agent12280 where
  dimensionLo := 12280
  dimensionHi := 12280
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2067959399 / 1000000000000 : ℝ)
  frameLo := (631644086867 / 1000000000000 : ℝ)
  frameHi := (364445406379 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12280]
  agentFrame_pos := by norm_num only [agent12280]
  worldRadius := (2067959399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12280]
  retainedCharge := (186927789 / 100000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (980953029 / 500000000000 : ℝ)
  lowerTail := (1121922387 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2418716619 / 250000000000 : ℝ)
  ledger := by
    have h : (595709131 / 500000000000 : ℚ) +
        (2574873981 / 250000000000000000 : ℚ) / (2067959399 / 1000000000000 : ℚ) ^ 2 +
        (186927789 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (980953029 / 500000000000 : ℚ) + (1121922387 / 500000000000 : ℚ) ≤
        (2418716619 / 250000000000 : ℚ) := by norm_num only
    have hc : (((595709131 / 500000000000 : ℚ) +
        (2574873981 / 250000000000000000 : ℚ) / (2067959399 / 1000000000000 : ℚ) ^ 2 +
        (186927789 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (980953029 / 500000000000 : ℚ) + (1121922387 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2418716619 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12280]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12280 :
    2 * 160 < 12280 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (439999933 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12280 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12281 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12281. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12281 : WorldParameters where
  hiddenCharge := (595684719 / 500000000000 : ℝ)
  frame := (631629259189 / 1000000000000 : ℝ)
  moment := (1029730139 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12281 : AgentParameters :=
  { agentLedgerParameters with
    charge := (467137869 / 250000000000 : ℝ)
    frame := (728870381893 / 500000000000 : ℝ)
    root := (4404233741 / 500000000000 : ℝ) }

noncomputable def scalar12281 : ScalarCertificate 12281 world12281 agent12281 where
  dimensionLo := 12281
  dimensionHi := 12281
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2068314799 / 1000000000000 : ℝ)
  frameLo := (631629259189 / 1000000000000 : ℝ)
  frameHi := (728870381893 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12281]
  agentFrame_pos := by norm_num only [agent12281]
  worldRadius := (2068314799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12281]
  retainedCharge := (467137869 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (980084323 / 500000000000 : ℝ)
  lowerTail := (224198797 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9669156423 / 1000000000000 : ℝ)
  ledger := by
    have h : (595684719 / 500000000000 : ℚ) +
        (1029730139 / 100000000000000000 : ℚ) / (2068314799 / 1000000000000 : ℚ) ^ 2 +
        (467137869 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (980084323 / 500000000000 : ℚ) + (224198797 / 100000000000 : ℚ) ≤
        (9669156423 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((595684719 / 500000000000 : ℚ) +
        (1029730139 / 100000000000000000 : ℚ) / (2068314799 / 1000000000000 : ℚ) ^ 2 +
        (467137869 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (980084323 / 500000000000 : ℚ) + (224198797 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9669156423 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12281]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12281 :
    2 * 160 < 12281 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999997549 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12281 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12282 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12282. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12282 : WorldParameters where
  hiddenCharge := (1191320627 / 1000000000000 : ℝ)
  frame := (63161443399 / 100000000000 : ℝ)
  moment := (1029510751 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12282 : AgentParameters :=
  { agentLedgerParameters with
    charge := (373565143 / 200000000000 : ℝ)
    frame := (364424980663 / 250000000000 : ℝ)
    root := (1100966913 / 125000000000 : ℝ) }

noncomputable def scalar12282 : ScalarCertificate 12282 world12282 agent12282 where
  dimensionLo := 12282
  dimensionHi := 12282
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2068670199 / 1000000000000 : ℝ)
  frameLo := (63161443399 / 100000000000 : ℝ)
  frameHi := (364424980663 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12282]
  agentFrame_pos := by norm_num only [agent12282]
  worldRadius := (2068670199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12282]
  retainedCharge := (373565143 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (489608249 / 250000000000 : ℝ)
  lowerTail := (560033237 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9663451511 / 1000000000000 : ℝ)
  ledger := by
    have h : (1191320627 / 1000000000000 : ℚ) +
        (1029510751 / 100000000000000000 : ℚ) / (2068670199 / 1000000000000 : ℚ) ^ 2 +
        (373565143 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (489608249 / 250000000000 : ℚ) + (560033237 / 250000000000 : ℚ) ≤
        (9663451511 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1191320627 / 1000000000000 : ℚ) +
        (1029510751 / 100000000000000000 : ℚ) / (2068670199 / 1000000000000 : ℚ) ^ 2 +
        (373565143 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (489608249 / 250000000000 : ℚ) + (560033237 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9663451511 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12282]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12282 :
    2 * 160 < 12282 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995623 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12282 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12283 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12283. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12283 : WorldParameters where
  hiddenCharge := (119127183 / 100000000000 : ℝ)
  frame := (157899902817 / 250000000000 : ℝ)
  moment := (5146457141 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12283 : AgentParameters :=
  { agentLedgerParameters with
    charge := (29173447 / 15625000000 : ℝ)
    frame := (291531819247 / 200000000000 : ℝ)
    root := (2201750839 / 250000000000 : ℝ) }

noncomputable def scalar12283 : ScalarCertificate 12283 world12283 agent12283 where
  dimensionLo := 12283
  dimensionHi := 12283
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2069025599 / 1000000000000 : ℝ)
  frameLo := (157899902817 / 250000000000 : ℝ)
  frameHi := (291531819247 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12283]
  agentFrame_pos := by norm_num only [agent12283]
  worldRadius := (2069025599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12283]
  retainedCharge := (29173447 / 15625000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (195669907 / 100000000000 : ℝ)
  lowerTail := (139892479 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (482887583 / 50000000000 : ℝ)
  ledger := by
    have h : (119127183 / 100000000000 : ℚ) +
        (5146457141 / 500000000000000000 : ℚ) / (2069025599 / 1000000000000 : ℚ) ^ 2 +
        (29173447 / 15625000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (195669907 / 100000000000 : ℚ) + (139892479 / 62500000000 : ℚ) ≤
        (482887583 / 50000000000 : ℚ) := by norm_num only
    have hc : (((119127183 / 100000000000 : ℚ) +
        (5146457141 / 500000000000000000 : ℚ) / (2069025599 / 1000000000000 : ℚ) ^ 2 +
        (29173447 / 15625000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (195669907 / 100000000000 : ℚ) + (139892479 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((482887583 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12283]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12283 :
    2 * 160 < 12283 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (343749953 / 31250000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12283 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12284 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12284. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12284 : WorldParameters where
  hiddenCharge := (595611523 / 500000000000 : ℝ)
  frame := (631584791023 / 1000000000000 : ℝ)
  moment := (10290721707 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12284 : AgentParameters :=
  { agentLedgerParameters with
    charge := (933188077 / 500000000000 : ℝ)
    frame := (728809148133 / 500000000000 : ℝ)
    root := (8806271563 / 1000000000000 : ℝ) }

noncomputable def scalar12284 : ScalarCertificate 12284 world12284 agent12284 where
  dimensionLo := 12284
  dimensionHi := 12284
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2069380999 / 1000000000000 : ℝ)
  frameLo := (631584791023 / 1000000000000 : ℝ)
  frameHi := (728809148133 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12284]
  agentFrame_pos := by norm_num only [agent12284]
  worldRadius := (2069380999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12284]
  retainedCharge := (933188077 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (488741713 / 250000000000 : ℝ)
  lowerTail := (1118214059 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9652056851 / 1000000000000 : ℝ)
  ledger := by
    have h : (595611523 / 500000000000 : ℚ) +
        (10290721707 / 1000000000000000000 : ℚ) / (2069380999 / 1000000000000 : ℚ) ^ 2 +
        (933188077 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (488741713 / 250000000000 : ℚ) + (1118214059 / 500000000000 : ℚ) ≤
        (9652056851 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((595611523 / 500000000000 : ℚ) +
        (10290721707 / 1000000000000000000 : ℚ) / (2069380999 / 1000000000000 : ℚ) ^ 2 +
        (933188077 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (488741713 / 250000000000 : ℚ) + (1118214059 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9652056851 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12284]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12284 :
    2 * 160 < 12284 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (5499997091 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12284 {← IO.monoMsNow}" : IO Unit)
