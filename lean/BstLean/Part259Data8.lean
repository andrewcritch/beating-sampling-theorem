import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12265 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12265. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12265 : WorldParameters where
  hiddenCharge := (1192152231 / 1000000000000 : ℝ)
  frame := (78983349981 / 125000000000 : ℝ)
  moment := (2066498499 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12265 : AgentParameters :=
  { agentLedgerParameters with
    charge := (376050607 / 200000000000 : ℝ)
    frame := (729197163321 / 500000000000 : ℝ)
    root := (137815841 / 15625000000 : ℝ) }

noncomputable def scalar12265 : ScalarCertificate 12265 world12265 agent12265 where
  dimensionLo := 12265
  dimensionHi := 12265
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2062633499 / 1000000000000 : ℝ)
  frameLo := (78983349981 / 125000000000 : ℝ)
  frameHi := (729197163321 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12265]
  agentFrame_pos := by norm_num only [agent12265]
  worldRadius := (2062633499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12265]
  retainedCharge := (376050607 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (497042569 / 250000000000 : ℝ)
  lowerTail := (2271899553 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (305034497 / 31250000000 : ℝ)
  ledger := by
    have h : (1192152231 / 1000000000000 : ℚ) +
        (2066498499 / 200000000000000000 : ℚ) / (2062633499 / 1000000000000 : ℚ) ^ 2 +
        (376050607 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (497042569 / 250000000000 : ℚ) + (2271899553 / 1000000000000 : ℚ) ≤
        (305034497 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1192152231 / 1000000000000 : ℚ) +
        (2066498499 / 200000000000000000 : ℚ) / (2062633499 / 1000000000000 : ℚ) ^ 2 +
        (376050607 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (497042569 / 250000000000 : ℚ) + (2271899553 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((305034497 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12265]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12265 :
    2 * 160 < 12265 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2749998517 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12265 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12266 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12266. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12266 : WorldParameters where
  hiddenCharge := (596051603 / 500000000000 : ℝ)
  frame := (15796298373 / 25000000000 : ℝ)
  moment := (2582572033 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12266 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1879516731 / 1000000000000 : ℝ)
    frame := (1458353507469 / 1000000000000 : ℝ)
    root := (220486949 / 25000000000 : ℝ) }

noncomputable def scalar12266 : ScalarCertificate 12266 world12266 agent12266 where
  dimensionLo := 12266
  dimensionHi := 12266
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2062988299 / 1000000000000 : ℝ)
  frameLo := (15796298373 / 25000000000 : ℝ)
  frameHi := (1458353507469 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12266]
  agentFrame_pos := by norm_num only [agent12266]
  worldRadius := (2062988299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12266]
  retainedCharge := (1879516731 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1986407577 / 1000000000000 : ℝ)
  lowerTail := (1135008763 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (48776603 / 5000000000 : ℝ)
  ledger := by
    have h : (596051603 / 500000000000 : ℚ) +
        (2582572033 / 250000000000000000 : ℚ) / (2062988299 / 1000000000000 : ℚ) ^ 2 +
        (1879516731 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1986407577 / 1000000000000 : ℚ) + (1135008763 / 500000000000 : ℚ) ≤
        (48776603 / 5000000000 : ℚ) := by norm_num only
    have hc : (((596051603 / 500000000000 : ℚ) +
        (2582572033 / 250000000000000000 : ℚ) / (2062988299 / 1000000000000 : ℚ) ^ 2 +
        (1879516731 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1986407577 / 1000000000000 : ℚ) + (1135008763 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((48776603 / 5000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12266]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12266 :
    2 * 160 < 12266 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999997959 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12266 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12267 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12267. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12267 : WorldParameters where
  hiddenCharge := (596027097 / 500000000000 : ℝ)
  frame := (3948981703 / 6250000000 : ℝ)
  moment := (5164042213 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12267 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1878781091 / 1000000000000 : ℝ)
    frame := (729156354503 / 500000000000 : ℝ)
    root := (1102342791 / 125000000000 : ℝ) }

noncomputable def scalar12267 : ScalarCertificate 12267 world12267 agent12267 where
  dimensionLo := 12267
  dimensionHi := 12267
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2063342999 / 1000000000000 : ℝ)
  frameLo := (3948981703 / 6250000000 : ℝ)
  frameHi := (729156354503 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12267]
  agentFrame_pos := by norm_num only [agent12267]
  worldRadius := (2063342999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12267]
  retainedCharge := (1878781091 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1984646553 / 1000000000000 : ℝ)
  lowerTail := (453627437 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9749542513 / 1000000000000 : ℝ)
  ledger := by
    have h : (596027097 / 500000000000 : ℚ) +
        (5164042213 / 500000000000000000 : ℚ) / (2063342999 / 1000000000000 : ℚ) ^ 2 +
        (1878781091 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1984646553 / 1000000000000 : ℚ) + (453627437 / 200000000000 : ℚ) ≤
        (9749542513 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((596027097 / 500000000000 : ℚ) +
        (5164042213 / 500000000000000000 : ℚ) / (2063342999 / 1000000000000 : ℚ) ^ 2 +
        (1878781091 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1984646553 / 1000000000000 : ℚ) + (453627437 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9749542513 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12267]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12267 :
    2 * 160 < 12267 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999999997 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12267 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12268 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12268. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12268 : WorldParameters where
  hiddenCharge := (238401039 / 200000000000 : ℝ)
  frame := (631822212527 / 1000000000000 : ℝ)
  moment := (10325881377 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12268 : AgentParameters :=
  { agentLedgerParameters with
    charge := (375609223 / 200000000000 : ℝ)
    frame := (729135968559 / 500000000000 : ℝ)
    root := (8818006927 / 1000000000000 : ℝ) }

noncomputable def scalar12268 : ScalarCertificate 12268 world12268 agent12268 where
  dimensionLo := 12268
  dimensionHi := 12268
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2063697799 / 1000000000000 : ℝ)
  frameLo := (631822212527 / 1000000000000 : ℝ)
  frameHi := (729135968559 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12268]
  agentFrame_pos := by norm_num only [agent12268]
  worldRadius := (2063697799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12268]
  retainedCharge := (375609223 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (396577493 / 200000000000 : ℝ)
  lowerTail := (2266258813 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (608985607 / 62500000000 : ℝ)
  ledger := by
    have h : (238401039 / 200000000000 : ℚ) +
        (10325881377 / 1000000000000000000 : ℚ) / (2063697799 / 1000000000000 : ℚ) ^ 2 +
        (375609223 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (396577493 / 200000000000 : ℚ) + (2266258813 / 1000000000000 : ℚ) ≤
        (608985607 / 62500000000 : ℚ) := by norm_num only
    have hc : (((238401039 / 200000000000 : ℚ) +
        (10325881377 / 1000000000000000000 : ℚ) / (2063697799 / 1000000000000 : ℚ) ^ 2 +
        (375609223 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (396577493 / 200000000000 : ℚ) + (2266258813 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((608985607 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12268]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12268 :
    2 * 160 < 12268 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999994129 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12268 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12269 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12269. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12269 : WorldParameters where
  hiddenCharge := (119195621 / 100000000000 : ℝ)
  frame := (631807355061 / 1000000000000 : ℝ)
  moment := (1290459873 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12269 : AgentParameters :=
  { agentLedgerParameters with
    charge := (9386559 / 5000000000 : ℝ)
    frame := (145823117417 / 100000000000 : ℝ)
    root := (2204317921 / 250000000000 : ℝ) }

noncomputable def scalar12269 : ScalarCertificate 12269 world12269 agent12269 where
  dimensionLo := 12269
  dimensionHi := 12269
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2064052599 / 1000000000000 : ℝ)
  frameLo := (631807355061 / 1000000000000 : ℝ)
  frameHi := (145823117417 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12269]
  agentFrame_pos := by norm_num only [agent12269]
  worldRadius := (2064052599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12269]
  retainedCharge := (9386559 / 5000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1981130011 / 1000000000000 : ℝ)
  lowerTail := (2264382083 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4869000901 / 500000000000 : ℝ)
  ledger := by
    have h : (119195621 / 100000000000 : ℚ) +
        (1290459873 / 125000000000000000 : ℚ) / (2064052599 / 1000000000000 : ℚ) ^ 2 +
        (9386559 / 5000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1981130011 / 1000000000000 : ℚ) + (2264382083 / 1000000000000 : ℚ) ≤
        (4869000901 / 500000000000 : ℚ) := by norm_num only
    have hc : (((119195621 / 100000000000 : ℚ) +
        (1290459873 / 125000000000000000 : ℚ) / (2064052599 / 1000000000000 : ℚ) ^ 2 +
        (9386559 / 5000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1981130011 / 1000000000000 : ℚ) + (2264382083 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4869000901 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12269]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12269 :
    2 * 160 < 12269 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999998403 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12269 {← IO.monoMsNow}" : IO Unit)
