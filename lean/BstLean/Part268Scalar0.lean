import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12350 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12350. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12350 : WorldParameters where
  hiddenCharge := (1856301 / 1562500000 : ℝ)
  frame := (126122419613 / 200000000000 : ℝ)
  moment := (10147442623 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12350 : AgentParameters :=
  { agentLedgerParameters with
    charge := (922892113 / 500000000000 : ℝ)
    frame := (1490987029929 / 1000000000000 : ℝ)
    root := (4373083601 / 500000000000 : ℝ) }

noncomputable def scalar12350 : ScalarCertificate 12350 world12350 agent12350 where
  dimensionLo := 12350
  dimensionHi := 12350
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2049776799 / 1000000000000 : ℝ)
  frameLo := (126122419613 / 200000000000 : ℝ)
  frameHi := (1490987029929 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12350]
  agentFrame_pos := by norm_num only [agent12350]
  worldRadius := (2049776799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12350]
  retainedCharge := (922892113 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1984534587 / 1000000000000 : ℝ)
  lowerTail := (1148398059 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9730294943 / 1000000000000 : ℝ)
  ledger := by
    have h : (1856301 / 1562500000 : ℚ) +
        (10147442623 / 1000000000000000000 : ℚ) / (2049776799 / 1000000000000 : ℚ) ^ 2 +
        (922892113 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1984534587 / 1000000000000 : ℚ) + (1148398059 / 500000000000 : ℚ) ≤
        (9730294943 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1856301 / 1562500000 : ℚ) +
        (10147442623 / 1000000000000000000 : ℚ) / (2049776799 / 1000000000000 : ℚ) ^ 2 +
        (922892113 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1984534587 / 1000000000000 : ℚ) + (1148398059 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9730294943 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12350]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12350 :
    2 * 160 < 12350 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995161 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12350 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12351 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12351. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12351 : WorldParameters where
  hiddenCharge := (1187984741 / 1000000000000 : ℝ)
  frame := (630597442271 / 1000000000000 : ℝ)
  moment := (10145293221 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12351 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1845080387 / 1000000000000 : ℝ)
    frame := (1490950452343 / 1000000000000 : ℝ)
    root := (4372706431 / 500000000000 : ℝ) }

noncomputable def scalar12351 : ScalarCertificate 12351 world12351 agent12351 where
  dimensionLo := 12351
  dimensionHi := 12351
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2050126299 / 1000000000000 : ℝ)
  frameLo := (630597442271 / 1000000000000 : ℝ)
  frameHi := (1490950452343 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12351]
  agentFrame_pos := by norm_num only [agent12351]
  worldRadius := (2050126299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12351]
  retainedCharge := (1845080387 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1982786543 / 1000000000000 : ℝ)
  lowerTail := (143432241 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (243114503 / 25000000000 : ℝ)
  ledger := by
    have h : (1187984741 / 1000000000000 : ℚ) +
        (10145293221 / 1000000000000000000 : ℚ) / (2050126299 / 1000000000000 : ℚ) ^ 2 +
        (1845080387 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1982786543 / 1000000000000 : ℚ) + (143432241 / 62500000000 : ℚ) ≤
        (243114503 / 25000000000 : ℚ) := by norm_num only
    have hc : (((1187984741 / 1000000000000 : ℚ) +
        (10145293221 / 1000000000000000000 : ℚ) / (2050126299 / 1000000000000 : ℚ) ^ 2 +
        (1845080387 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1982786543 / 1000000000000 : ℚ) + (143432241 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((243114503 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12351]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12351 :
    2 * 160 < 12351 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999887 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12351 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12352 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12352. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12352 : WorldParameters where
  hiddenCharge := (148492107 / 125000000000 : ℝ)
  frame := (63058278891 / 100000000000 : ℝ)
  moment := (2028628891 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12352 : AgentParameters :=
  { agentLedgerParameters with
    charge := (922188589 / 500000000000 : ℝ)
    frame := (298182781003 / 200000000000 : ℝ)
    root := (2186164711 / 250000000000 : ℝ) }

noncomputable def scalar12352 : ScalarCertificate 12352 world12352 agent12352 where
  dimensionLo := 12352
  dimensionHi := 12352
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2050475699 / 1000000000000 : ℝ)
  frameLo := (63058278891 / 100000000000 : ℝ)
  frameHi := (298182781003 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12352]
  agentFrame_pos := by norm_num only [agent12352]
  worldRadius := (2050475699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12352]
  retainedCharge := (922188589 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1981040309 / 1000000000000 : ℝ)
  lowerTail := (286629679 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1943774149 / 200000000000 : ℝ)
  ledger := by
    have h : (148492107 / 125000000000 : ℚ) +
        (2028628891 / 200000000000000000 : ℚ) / (2050475699 / 1000000000000 : ℚ) ^ 2 +
        (922188589 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1981040309 / 1000000000000 : ℚ) + (286629679 / 125000000000 : ℚ) ≤
        (1943774149 / 200000000000 : ℚ) := by norm_num only
    have hc : (((148492107 / 125000000000 : ℚ) +
        (2028628891 / 200000000000000000 : ℚ) / (2050475699 / 1000000000000 : ℚ) ^ 2 +
        (922188589 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1981040309 / 1000000000000 : ℚ) + (286629679 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1943774149 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12352]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12352 :
    2 * 160 < 12352 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199998917 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12352 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12353 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12353. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12353 : WorldParameters where
  hiddenCharge := (1187888983 / 1000000000000 : ℝ)
  frame := (31528406899 / 50000000000 : ℝ)
  moment := (405639853 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12353 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1843674599 / 1000000000000 : ℝ)
    frame := (1490877375927 / 1000000000000 : ℝ)
    root := (2185976251 / 250000000000 : ℝ) }

noncomputable def scalar12353 : ScalarCertificate 12353 world12353 agent12353 where
  dimensionLo := 12353
  dimensionHi := 12353
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2050825299 / 1000000000000 : ℝ)
  frameLo := (31528406899 / 50000000000 : ℝ)
  frameHi := (1490877375927 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12353]
  agentFrame_pos := by norm_num only [agent12353]
  worldRadius := (2050825299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12353]
  retainedCharge := (1843674599 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (989647997 / 500000000000 : ℝ)
  lowerTail := (286395121 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4856583169 / 500000000000 : ℝ)
  ledger := by
    have h : (1187888983 / 1000000000000 : ℚ) +
        (405639853 / 40000000000000000 : ℚ) / (2050825299 / 1000000000000 : ℚ) ^ 2 +
        (1843674599 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (989647997 / 500000000000 : ℚ) + (286395121 / 125000000000 : ℚ) ≤
        (4856583169 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1187888983 / 1000000000000 : ℚ) +
        (405639853 / 40000000000000000 : ℚ) / (2050825299 / 1000000000000 : ℚ) ^ 2 +
        (1843674599 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (989647997 / 500000000000 : ℚ) + (286395121 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4856583169 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12353]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12353 :
    2 * 160 < 12353 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199998873 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12353 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12354 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12354. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12354 : WorldParameters where
  hiddenCharge := (1187841123 / 1000000000000 : ℝ)
  frame := (630553489481 / 1000000000000 : ℝ)
  moment := (1013884883 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12354 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1842972647 / 1000000000000 : ℝ)
    frame := (1490840865063 / 1000000000000 : ℝ)
    root := (4371575707 / 500000000000 : ℝ) }

noncomputable def scalar12354 : ScalarCertificate 12354 world12354 agent12354 where
  dimensionLo := 12354
  dimensionHi := 12354
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2051174899 / 1000000000000 : ℝ)
  frameLo := (630553489481 / 1000000000000 : ℝ)
  frameHi := (1490840865063 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12354]
  agentFrame_pos := by norm_num only [agent12354]
  worldRadius := (2051174899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12354]
  retainedCharge := (1842972647 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (247194181 / 125000000000 : ℝ)
  lowerTail := (286160787 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (606716691 / 62500000000 : ℝ)
  ledger := by
    have h : (1187841123 / 1000000000000 : ℚ) +
        (1013884883 / 100000000000000000 : ℚ) / (2051174899 / 1000000000000 : ℚ) ^ 2 +
        (1842972647 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (247194181 / 125000000000 : ℚ) + (286160787 / 125000000000 : ℚ) ≤
        (606716691 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1187841123 / 1000000000000 : ℚ) +
        (1013884883 / 100000000000000000 : ℚ) / (2051174899 / 1000000000000 : ℚ) ^ 2 +
        (1842972647 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (247194181 / 125000000000 : ℚ) + (286160787 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((606716691 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12354]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12354 :
    2 * 160 < 12354 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998189 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12354 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12355 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12355. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12355 : WorldParameters where
  hiddenCharge := (1187793277 / 1000000000000 : ℝ)
  frame := (630538843413 / 1000000000000 : ℝ)
  moment := (10136701971 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12355 : AgentParameters :=
  { agentLedgerParameters with
    charge := (460567831 / 250000000000 : ℝ)
    frame := (372701094603 / 250000000000 : ℝ)
    root := (1748479629 / 200000000000 : ℝ) }

noncomputable def scalar12355 : ScalarCertificate 12355 world12355 agent12355 where
  dimensionLo := 12355
  dimensionHi := 12355
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2051524399 / 1000000000000 : ℝ)
  frameLo := (630538843413 / 1000000000000 : ℝ)
  frameHi := (372701094603 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12355]
  agentFrame_pos := by norm_num only [agent12355]
  worldRadius := (2051524399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12355]
  retainedCharge := (460567831 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1975812671 / 1000000000000 : ℝ)
  lowerTail := (457482683 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1212721641 / 125000000000 : ℝ)
  ledger := by
    have h : (1187793277 / 1000000000000 : ℚ) +
        (10136701971 / 1000000000000000000 : ℚ) / (2051524399 / 1000000000000 : ℚ) ^ 2 +
        (460567831 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1975812671 / 1000000000000 : ℚ) + (457482683 / 200000000000 : ℚ) ≤
        (1212721641 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1187793277 / 1000000000000 : ℚ) +
        (10136701971 / 1000000000000000000 : ℚ) / (2051524399 / 1000000000000 : ℚ) ^ 2 +
        (460567831 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1975812671 / 1000000000000 : ℚ) + (457482683 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1212721641 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12355]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12355 :
    2 * 160 < 12355 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999997 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12355 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12356 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12356. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12356 : WorldParameters where
  hiddenCharge := (1187745443 / 1000000000000 : ℝ)
  frame := (25220967991 / 40000000000 : ℝ)
  moment := (10134555747 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12356 : AgentParameters :=
  { agentLedgerParameters with
    charge := (184157063 / 100000000000 : ℝ)
    frame := (372691978989 / 250000000000 : ℝ)
    root := (4370822527 / 500000000000 : ℝ) }

noncomputable def scalar12356 : ScalarCertificate 12356 world12356 agent12356 where
  dimensionLo := 12356
  dimensionHi := 12356
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2051873899 / 1000000000000 : ℝ)
  frameLo := (25220967991 / 40000000000 : ℝ)
  frameHi := (372691978989 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12356]
  agentFrame_pos := by norm_num only [agent12356]
  worldRadius := (2051873899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12356]
  retainedCharge := (184157063 / 100000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (987036807 / 500000000000 : ℝ)
  lowerTail := (457108457 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9696084229 / 1000000000000 : ℝ)
  ledger := by
    have h : (1187745443 / 1000000000000 : ℚ) +
        (10134555747 / 1000000000000000000 : ℚ) / (2051873899 / 1000000000000 : ℚ) ^ 2 +
        (184157063 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (987036807 / 500000000000 : ℚ) + (457108457 / 200000000000 : ℚ) ≤
        (9696084229 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1187745443 / 1000000000000 : ℚ) +
        (10134555747 / 1000000000000000000 : ℚ) / (2051873899 / 1000000000000 : ℚ) ^ 2 +
        (184157063 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (987036807 / 500000000000 : ℚ) + (457108457 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9696084229 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12356]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12356 :
    2 * 160 < 12356 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999863 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12356 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12357 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12357. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12357 : WorldParameters where
  hiddenCharge := (1187697623 / 1000000000000 : ℝ)
  frame := (315254779283 / 500000000000 : ℝ)
  moment := (5066205079 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12357 : AgentParameters :=
  { agentLedgerParameters with
    charge := (11505441 / 6250000000 : ℝ)
    frame := (745365738841 / 500000000000 : ℝ)
    root := (2185223053 / 250000000000 : ℝ) }

noncomputable def scalar12357 : ScalarCertificate 12357 world12357 agent12357 where
  dimensionLo := 12357
  dimensionHi := 12357
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2052223499 / 1000000000000 : ℝ)
  frameLo := (315254779283 / 500000000000 : ℝ)
  frameHi := (745365738841 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12357]
  agentFrame_pos := by norm_num only [agent12357]
  worldRadius := (2052223499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12357]
  retainedCharge := (11505441 / 6250000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1972336467 / 1000000000000 : ℝ)
  lowerTail := (456734621 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (37853127 / 3906250000 : ℝ)
  ledger := by
    have h : (1187697623 / 1000000000000 : ℚ) +
        (5066205079 / 500000000000000000 : ℚ) / (2052223499 / 1000000000000 : ℚ) ^ 2 +
        (11505441 / 6250000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1972336467 / 1000000000000 : ℚ) + (456734621 / 200000000000 : ℚ) ≤
        (37853127 / 3906250000 : ℚ) := by norm_num only
    have hc : (((1187697623 / 1000000000000 : ℚ) +
        (5066205079 / 500000000000000000 : ℚ) / (2052223499 / 1000000000000 : ℚ) ^ 2 +
        (11505441 / 6250000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1972336467 / 1000000000000 : ℚ) + (456734621 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((37853127 / 3906250000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12357]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12357 :
    2 * 160 < 12357 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999673 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12357 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12358 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12358. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12358 : WorldParameters where
  hiddenCharge := (237529963 / 200000000000 : ℝ)
  frame := (126098983957 / 200000000000 : ℝ)
  moment := (2532566301 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12358 : AgentParameters :=
  { agentLedgerParameters with
    charge := (920085559 / 500000000000 : ℝ)
    frame := (59627802303 / 40000000000 : ℝ)
    root := (437006981 / 50000000000 : ℝ) }

noncomputable def scalar12358 : ScalarCertificate 12358 world12358 agent12358 where
  dimensionLo := 12358
  dimensionHi := 12358
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2052572999 / 1000000000000 : ℝ)
  frameLo := (126098983957 / 200000000000 : ℝ)
  frameHi := (59627802303 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12358]
  agentFrame_pos := by norm_num only [agent12358]
  worldRadius := (2052572999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12358]
  retainedCharge := (920085559 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (246325121 / 125000000000 : ℝ)
  lowerTail := (2281805589 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9684721897 / 1000000000000 : ℝ)
  ledger := by
    have h : (237529963 / 200000000000 : ℚ) +
        (2532566301 / 250000000000000000 : ℚ) / (2052572999 / 1000000000000 : ℚ) ^ 2 +
        (920085559 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (246325121 / 125000000000 : ℚ) + (2281805589 / 1000000000000 : ℚ) ≤
        (9684721897 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((237529963 / 200000000000 : ℚ) +
        (2532566301 / 250000000000000000 : ℚ) / (2052572999 / 1000000000000 : ℚ) ^ 2 +
        (920085559 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (246325121 / 125000000000 : ℚ) + (2281805589 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9684721897 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12358]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12358 :
    2 * 160 < 12358 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998989 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12358 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12359 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12359. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12359 : WorldParameters where
  hiddenCharge := (1187602021 / 1000000000000 : ℝ)
  frame := (630480283433 / 1000000000000 : ℝ)
  moment := (2532030221 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12359 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1839472301 / 1000000000000 : ℝ)
    frame := (1490658661619 / 1000000000000 : ℝ)
    root := (2184846837 / 250000000000 : ℝ) }

noncomputable def scalar12359 : ScalarCertificate 12359 world12359 agent12359 where
  dimensionLo := 12359
  dimensionHi := 12359
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2052922499 / 1000000000000 : ℝ)
  frameLo := (630480283433 / 1000000000000 : ℝ)
  frameHi := (1490658661619 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12359]
  agentFrame_pos := by norm_num only [agent12359]
  worldRadius := (2052922499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12359]
  retainedCharge := (1839472301 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (984433671 / 500000000000 : ℝ)
  lowerTail := (284992497 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4839524307 / 500000000000 : ℝ)
  ledger := by
    have h : (1187602021 / 1000000000000 : ℚ) +
        (2532030221 / 250000000000000000 : ℚ) / (2052922499 / 1000000000000 : ℚ) ^ 2 +
        (1839472301 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (984433671 / 500000000000 : ℚ) + (284992497 / 125000000000 : ℚ) ≤
        (4839524307 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1187602021 / 1000000000000 : ℚ) +
        (2532030221 / 250000000000000000 : ℚ) / (2052922499 / 1000000000000 : ℚ) ^ 2 +
        (1839472301 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (984433671 / 500000000000 : ℚ) + (284992497 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4839524307 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12359]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12359 :
    2 * 160 < 12359 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (549999923 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12359 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12360 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12360. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12360 : WorldParameters where
  hiddenCharge := (3711107 / 3125000000 : ℝ)
  frame := (157616412377 / 250000000000 : ℝ)
  moment := (5062988599 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12360 : AgentParameters :=
  { agentLedgerParameters with
    charge := (183877411 / 100000000000 : ℝ)
    frame := (29810735719 / 20000000000 : ℝ)
    root := (8738635253 / 1000000000000 : ℝ) }

noncomputable def scalar12360 : ScalarCertificate 12360 world12360 agent12360 where
  dimensionLo := 12360
  dimensionHi := 12360
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2053379599 / 1000000000000 : ℝ)
  frameLo := (157616412377 / 250000000000 : ℝ)
  frameHi := (29810735719 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12360]
  agentFrame_pos := by norm_num only [agent12360]
  worldRadius := (2053379599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12360]
  retainedCharge := (183877411 / 100000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (98338621 / 50000000000 : ℝ)
  lowerTail := (2277619093 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2418077151 / 250000000000 : ℝ)
  ledger := by
    have h : (3711107 / 3125000000 : ℚ) +
        (5062988599 / 500000000000000000 : ℚ) / (2053379599 / 1000000000000 : ℚ) ^ 2 +
        (183877411 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (98338621 / 50000000000 : ℚ) + (2277619093 / 1000000000000 : ℚ) ≤
        (2418077151 / 250000000000 : ℚ) := by norm_num only
    have hc : (((3711107 / 3125000000 : ℚ) +
        (5062988599 / 500000000000000000 : ℚ) / (2053379599 / 1000000000000 : ℚ) ^ 2 +
        (183877411 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (98338621 / 50000000000 : ℚ) + (2277619093 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2418077151 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12360]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12360 :
    2 * 160 < 12360 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995771 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12360 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12361 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12361. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12361 : WorldParameters where
  hiddenCharge := (1187506471 / 1000000000000 : ℝ)
  frame := (630451018009 / 1000000000000 : ℝ)
  moment := (5061917073 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12361 : AgentParameters :=
  { agentLedgerParameters with
    charge := (919038271 / 500000000000 : ℝ)
    frame := (1490500433309 / 1000000000000 : ℝ)
    root := (8737883407 / 1000000000000 : ℝ) }

noncomputable def scalar12361 : ScalarCertificate 12361 world12361 agent12361 where
  dimensionLo := 12361
  dimensionHi := 12361
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2053729099 / 1000000000000 : ℝ)
  frameLo := (630451018009 / 1000000000000 : ℝ)
  frameHi := (1490500433309 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12361]
  agentFrame_pos := by norm_num only [agent12361]
  worldRadius := (2053729099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12361]
  retainedCharge := (919038271 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (49126063 / 25000000000 : ℝ)
  lowerTail := (455151461 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4833323079 / 500000000000 : ℝ)
  ledger := by
    have h : (1187506471 / 1000000000000 : ℚ) +
        (5061917073 / 500000000000000000 : ℚ) / (2053729099 / 1000000000000 : ℚ) ^ 2 +
        (919038271 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (49126063 / 25000000000 : ℚ) + (455151461 / 200000000000 : ℚ) ≤
        (4833323079 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1187506471 / 1000000000000 : ℚ) +
        (5061917073 / 500000000000000000 : ℚ) / (2053729099 / 1000000000000 : ℚ) ^ 2 +
        (919038271 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (49126063 / 25000000000 : ℚ) + (455151461 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4833323079 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12361]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12361 :
    2 * 160 < 12361 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999239 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12361 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12362 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12362. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12362 : WorldParameters where
  hiddenCharge := (296864679 / 250000000000 : ℝ)
  frame := (78804548617 / 125000000000 : ℝ)
  moment := (10121691727 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12362 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1837379599 / 1000000000000 : ℝ)
    frame := (745232052387 / 500000000000 : ℝ)
    root := (873713181 / 100000000000 : ℝ) }

noncomputable def scalar12362 : ScalarCertificate 12362 world12362 agent12362 where
  dimensionLo := 12362
  dimensionHi := 12362
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2054078699 / 1000000000000 : ℝ)
  frameLo := (78804548617 / 125000000000 : ℝ)
  frameHi := (745232052387 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12362]
  agentFrame_pos := by norm_num only [agent12362]
  worldRadius := (2054078699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12362]
  retainedCharge := (1837379599 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1963314521 / 1000000000000 : ℝ)
  lowerTail := (142118591 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4830494433 / 500000000000 : ℝ)
  ledger := by
    have h : (296864679 / 250000000000 : ℚ) +
        (10121691727 / 1000000000000000000 : ℚ) / (2054078699 / 1000000000000 : ℚ) ^ 2 +
        (1837379599 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1963314521 / 1000000000000 : ℚ) + (142118591 / 62500000000 : ℚ) ≤
        (4830494433 / 500000000000 : ℚ) := by norm_num only
    have hc : (((296864679 / 250000000000 : ℚ) +
        (10121691727 / 1000000000000000000 : ℚ) / (2054078699 / 1000000000000 : ℚ) ^ 2 +
        (1837379599 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1963314521 / 1000000000000 : ℚ) + (142118591 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((4830494433 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12362]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12362 :
    2 * 160 < 12362 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995931 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12362 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12363 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12363. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12363 : WorldParameters where
  hiddenCharge := (1187410973 / 1000000000000 : ℝ)
  frame := (630421762289 / 1000000000000 : ℝ)
  moment := (5059774971 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12363 : AgentParameters :=
  { agentLedgerParameters with
    charge := (918341639 / 500000000000 : ℝ)
    frame := (745213897167 / 500000000000 : ℝ)
    root := (2184095133 / 250000000000 : ℝ) }

noncomputable def scalar12363 : ScalarCertificate 12363 world12363 agent12363 where
  dimensionLo := 12363
  dimensionHi := 12363
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2054428299 / 1000000000000 : ℝ)
  frameLo := (630421762289 / 1000000000000 : ℝ)
  frameHi := (745213897167 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12363]
  agentFrame_pos := by norm_num only [agent12363]
  worldRadius := (2054428299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12363]
  retainedCharge := (918341639 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1961588351 / 1000000000000 : ℝ)
  lowerTail := (113601973 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4827668403 / 500000000000 : ℝ)
  ledger := by
    have h : (1187410973 / 1000000000000 : ℚ) +
        (5059774971 / 500000000000000000 : ℚ) / (2054428299 / 1000000000000 : ℚ) ^ 2 +
        (918341639 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1961588351 / 1000000000000 : ℚ) + (113601973 / 50000000000 : ℚ) ≤
        (4827668403 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1187410973 / 1000000000000 : ℚ) +
        (5059774971 / 500000000000000000 : ℚ) / (2054428299 / 1000000000000 : ℚ) ^ 2 +
        (918341639 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1961588351 / 1000000000000 : ℚ) + (113601973 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4827668403 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12363]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12363 :
    2 * 160 < 12363 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999747 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12363 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12364 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12364. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12364 : WorldParameters where
  hiddenCharge := (296840811 / 250000000000 : ℝ)
  frame := (315203569033 / 500000000000 : ℝ)
  moment := (10117408791 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12364 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1835987579 / 1000000000000 : ℝ)
    frame := (1490391190067 / 1000000000000 : ℝ)
    root := (8735629431 / 1000000000000 : ℝ) }

noncomputable def scalar12364 : ScalarCertificate 12364 world12364 agent12364 where
  dimensionLo := 12364
  dimensionHi := 12364
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2054778199 / 1000000000000 : ℝ)
  frameLo := (315203569033 / 500000000000 : ℝ)
  frameHi := (1490391190067 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12364]
  agentFrame_pos := by norm_num only [agent12364]
  worldRadius := (2054778199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12364]
  retainedCharge := (1835987579 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (78394497 / 40000000000 : ℝ)
  lowerTail := (2270181383 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9649685757 / 1000000000000 : ℝ)
  ledger := by
    have h : (296840811 / 250000000000 : ℚ) +
        (10117408791 / 1000000000000000000 : ℚ) / (2054778199 / 1000000000000 : ℚ) ^ 2 +
        (1835987579 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (78394497 / 40000000000 : ℚ) + (2270181383 / 1000000000000 : ℚ) ≤
        (9649685757 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((296840811 / 250000000000 : ℚ) +
        (10117408791 / 1000000000000000000 : ℚ) / (2054778199 / 1000000000000 : ℚ) ^ 2 +
        (1835987579 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (78394497 / 40000000000 : ℚ) + (2270181383 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9649685757 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12364]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12364 :
    2 * 160 < 12364 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999371 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12364 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12365 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12365. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12365 : WorldParameters where
  hiddenCharge := (1187315527 / 1000000000000 : ℝ)
  frame := (157598129067 / 250000000000 : ℝ)
  moment := (632204267 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12365 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1835292503 / 1000000000000 : ℝ)
    frame := (298070917179 / 200000000000 : ℝ)
    root := (8734878577 / 1000000000000 : ℝ) }

noncomputable def scalar12365 : ScalarCertificate 12365 world12365 agent12365 where
  dimensionLo := 12365
  dimensionHi := 12365
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2055128299 / 1000000000000 : ℝ)
  frameLo := (157598129067 / 250000000000 : ℝ)
  frameHi := (298070917179 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12365]
  agentFrame_pos := by norm_num only [agent12365]
  worldRadius := (2055128299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12365]
  retainedCharge := (1835292503 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1958138371 / 1000000000000 : ℝ)
  lowerTail := (2268325197 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (75344059 / 7812500000 : ℝ)
  ledger := by
    have h : (1187315527 / 1000000000000 : ℚ) +
        (632204267 / 62500000000000000 : ℚ) / (2055128299 / 1000000000000 : ℚ) ^ 2 +
        (1835292503 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1958138371 / 1000000000000 : ℚ) + (2268325197 / 1000000000000 : ℚ) ≤
        (75344059 / 7812500000 : ℚ) := by norm_num only
    have hc : (((1187315527 / 1000000000000 : ℚ) +
        (632204267 / 62500000000000000 : ℚ) / (2055128299 / 1000000000000 : ℚ) ^ 2 +
        (1835292503 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1958138371 / 1000000000000 : ℚ) + (2268325197 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((75344059 / 7812500000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12365]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12365 :
    2 * 160 < 12365 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996581 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12365 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12366 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12366. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12366 : WorldParameters where
  hiddenCharge := (74204239 / 62500000000 : ℝ)
  frame := (630377896893 / 1000000000000 : ℝ)
  moment := (5056564193 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12366 : AgentParameters :=
  { agentLedgerParameters with
    charge := (57331189 / 31250000000 : ℝ)
    frame := (372579501449 / 250000000000 : ℝ)
    root := (2183531993 / 250000000000 : ℝ) }

noncomputable def scalar12366 : ScalarCertificate 12366 world12366 agent12366 where
  dimensionLo := 12366
  dimensionHi := 12366
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2055478299 / 1000000000000 : ℝ)
  frameLo := (630377896893 / 1000000000000 : ℝ)
  frameHi := (372579501449 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12366]
  agentFrame_pos := by norm_num only [agent12366]
  worldRadius := (2055478299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12366]
  retainedCharge := (57331189 / 31250000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (391283197 / 200000000000 : ℝ)
  lowerTail := (1133235351 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2409599621 / 250000000000 : ℝ)
  ledger := by
    have h : (74204239 / 62500000000 : ℚ) +
        (5056564193 / 500000000000000000 : ℚ) / (2055478299 / 1000000000000 : ℚ) ^ 2 +
        (57331189 / 31250000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (391283197 / 200000000000 : ℚ) + (1133235351 / 500000000000 : ℚ) ≤
        (2409599621 / 250000000000 : ℚ) := by norm_num only
    have hc : (((74204239 / 62500000000 : ℚ) +
        (5056564193 / 500000000000000000 : ℚ) / (2055478299 / 1000000000000 : ℚ) ^ 2 +
        (57331189 / 31250000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (391283197 / 200000000000 : ℚ) + (1133235351 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2409599621 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12366]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12366 :
    2 * 160 < 12366 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999699 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12366 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12367 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12367. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12367 : WorldParameters where
  hiddenCharge := (593610067 / 500000000000 : ℝ)
  frame := (630363279941 / 1000000000000 : ℝ)
  moment := (2527747283 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12367 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1833904213 / 1000000000000 : ℝ)
    frame := (372570362439 / 250000000000 : ℝ)
    root := (4366688807 / 500000000000 : ℝ) }

noncomputable def scalar12367 : ScalarCertificate 12367 world12367 agent12367 where
  dimensionLo := 12367
  dimensionHi := 12367
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2055828299 / 1000000000000 : ℝ)
  frameLo := (630363279941 / 1000000000000 : ℝ)
  frameHi := (372570362439 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12367]
  agentFrame_pos := by norm_num only [agent12367]
  worldRadius := (2055828299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12367]
  retainedCharge := (1833904213 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1954695377 / 1000000000000 : ℝ)
  lowerTail := (2264618017 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (192655251 / 20000000000 : ℝ)
  ledger := by
    have h : (593610067 / 500000000000 : ℚ) +
        (2527747283 / 250000000000000000 : ℚ) / (2055828299 / 1000000000000 : ℚ) ^ 2 +
        (1833904213 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1954695377 / 1000000000000 : ℚ) + (2264618017 / 1000000000000 : ℚ) ≤
        (192655251 / 20000000000 : ℚ) := by norm_num only
    have hc : (((593610067 / 500000000000 : ℚ) +
        (2527747283 / 250000000000000000 : ℚ) / (2055828299 / 1000000000000 : ℚ) ^ 2 +
        (1833904213 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1954695377 / 1000000000000 : ℚ) + (2264618017 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((192655251 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12367]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12367 :
    2 * 160 < 12367 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999233 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12367 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12368 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12368. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12368 : WorldParameters where
  hiddenCharge := (148396557 / 125000000000 : ℝ)
  frame := (630348665411 / 1000000000000 : ℝ)
  moment := (1010885051 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12368 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1833210999 / 1000000000000 : ℝ)
    frame := (1490244917759 / 1000000000000 : ℝ)
    root := (349305103 / 40000000000 : ℝ) }

noncomputable def scalar12368 : ScalarCertificate 12368 world12368 agent12368 where
  dimensionLo := 12368
  dimensionHi := 12368
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2056178399 / 1000000000000 : ℝ)
  frameLo := (630348665411 / 1000000000000 : ℝ)
  frameHi := (1490244917759 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12368]
  agentFrame_pos := by norm_num only [agent12368]
  worldRadius := (2056178399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12368]
  retainedCharge := (1833210999 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (61030523 / 31250000000 : ℝ)
  lowerTail := (2262767339 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (96271319 / 10000000000 : ℝ)
  ledger := by
    have h : (148396557 / 125000000000 : ℚ) +
        (1010885051 / 100000000000000000 : ℚ) / (2056178399 / 1000000000000 : ℚ) ^ 2 +
        (1833210999 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (61030523 / 31250000000 : ℚ) + (2262767339 / 1000000000000 : ℚ) ≤
        (96271319 / 10000000000 : ℚ) := by norm_num only
    have hc : (((148396557 / 125000000000 : ℚ) +
        (1010885051 / 100000000000000000 : ℚ) / (2056178399 / 1000000000000 : ℚ) ^ 2 +
        (1833210999 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (61030523 / 31250000000 : ℚ) + (2262767339 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((96271319 / 10000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12368]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12368 :
    2 * 160 < 12368 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994079 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12368 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12369 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12369. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12369 : WorldParameters where
  hiddenCharge := (148390599 / 125000000000 : ℝ)
  frame := (315167026651 / 500000000000 : ℝ)
  moment := (10106712521 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12369 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1832518403 / 1000000000000 : ℝ)
    frame := (745104201897 / 500000000000 : ℝ)
    root := (545742357 / 62500000000 : ℝ) }

noncomputable def scalar12369 : ScalarCertificate 12369 world12369 agent12369 where
  dimensionLo := 12369
  dimensionHi := 12369
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2056528399 / 1000000000000 : ℝ)
  frameLo := (315167026651 / 500000000000 : ℝ)
  frameHi := (745104201897 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12369]
  agentFrame_pos := by norm_num only [agent12369]
  worldRadius := (2056528399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12369]
  retainedCharge := (1832518403 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (487814911 / 250000000000 : ℝ)
  lowerTail := (1130459113 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9621506139 / 1000000000000 : ℝ)
  ledger := by
    have h : (148390599 / 125000000000 : ℚ) +
        (10106712521 / 1000000000000000000 : ℚ) / (2056528399 / 1000000000000 : ℚ) ^ 2 +
        (1832518403 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (487814911 / 250000000000 : ℚ) + (1130459113 / 500000000000 : ℚ) ≤
        (9621506139 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((148390599 / 125000000000 : ℚ) +
        (10106712521 / 1000000000000000000 : ℚ) / (2056528399 / 1000000000000 : ℚ) ^ 2 +
        (1832518403 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (487814911 / 250000000000 : ℚ) + (1130459113 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9621506139 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12369]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12369 :
    2 * 160 < 12369 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998351 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12369 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12370 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12370. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12370 : WorldParameters where
  hiddenCharge := (59353857 / 50000000000 : ℝ)
  frame := (315159721807 / 500000000000 : ℝ)
  moment := (10104575163 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12370 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1831826427 / 1000000000000 : ℝ)
    frame := (298017307487 / 200000000000 : ℝ)
    root := (272847753 / 31250000000 : ℝ) }

noncomputable def scalar12370 : ScalarCertificate 12370 world12370 agent12370 where
  dimensionLo := 12370
  dimensionHi := 12370
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2056985999 / 1000000000000 : ℝ)
  frameLo := (315159721807 / 500000000000 : ℝ)
  frameHi := (298017307487 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12370]
  agentFrame_pos := by norm_num only [agent12370]
  worldRadius := (2056985999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12370]
  retainedCharge := (1831826427 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (487296151 / 250000000000 : ℝ)
  lowerTail := (2258617779 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4807411387 / 500000000000 : ℝ)
  ledger := by
    have h : (59353857 / 50000000000 : ℚ) +
        (10104575163 / 1000000000000000000 : ℚ) / (2056985999 / 1000000000000 : ℚ) ^ 2 +
        (1831826427 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (487296151 / 250000000000 : ℚ) + (2258617779 / 1000000000000 : ℚ) ≤
        (4807411387 / 500000000000 : ℚ) := by norm_num only
    have hc : (((59353857 / 50000000000 : ℚ) +
        (10104575163 / 1000000000000000000 : ℚ) / (2056985999 / 1000000000000 : ℚ) ^ 2 +
        (1831826427 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (487296151 / 250000000000 : ℚ) + (2258617779 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4807411387 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12370]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12370 :
    2 * 160 < 12370 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998009 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12370 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12371 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12371. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12371 : WorldParameters where
  hiddenCharge := (1187029501 / 1000000000000 : ℝ)
  frame := (630304836347 / 1000000000000 : ℝ)
  moment := (10102438437 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12371 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1831135069 / 1000000000000 : ℝ)
    frame := (29801001451 / 20000000000 : ℝ)
    root := (8730378727 / 1000000000000 : ℝ) }

noncomputable def scalar12371 : ScalarCertificate 12371 world12371 agent12371 where
  dimensionLo := 12371
  dimensionHi := 12371
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2057336099 / 1000000000000 : ℝ)
  frameLo := (630304836347 / 1000000000000 : ℝ)
  frameHi := (29801001451 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12371]
  agentFrame_pos := by norm_num only [agent12371]
  worldRadius := (2057336099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12371]
  retainedCharge := (1831135069 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1947471423 / 1000000000000 : ℝ)
  lowerTail := (564193173 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4804603989 / 500000000000 : ℝ)
  ledger := by
    have h : (1187029501 / 1000000000000 : ℚ) +
        (10102438437 / 1000000000000000000 : ℚ) / (2057336099 / 1000000000000 : ℚ) ^ 2 +
        (1831135069 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1947471423 / 1000000000000 : ℚ) + (564193173 / 250000000000 : ℚ) ≤
        (4804603989 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1187029501 / 1000000000000 : ℚ) +
        (10102438437 / 1000000000000000000 : ℚ) / (2057336099 / 1000000000000 : ℚ) ^ 2 +
        (1831135069 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1947471423 / 1000000000000 : ℚ) + (564193173 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4804603989 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12371]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12371 :
    2 * 160 < 12371 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999797 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12371 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12372 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12372. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12372 : WorldParameters where
  hiddenCharge := (296745469 / 250000000000 : ℝ)
  frame := (630290231499 / 1000000000000 : ℝ)
  moment := (5050151171 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12372 : AgentParameters :=
  { agentLedgerParameters with
    charge := (228805541 / 125000000000 : ℝ)
    frame := (1490013631649 / 1000000000000 : ℝ)
    root := (2182407401 / 250000000000 : ℝ) }

noncomputable def scalar12372 : ScalarCertificate 12372 world12372 agent12372 where
  dimensionLo := 12372
  dimensionHi := 12372
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2057686099 / 1000000000000 : ℝ)
  frameLo := (630290231499 / 1000000000000 : ℝ)
  frameHi := (1490013631649 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12372]
  agentFrame_pos := by norm_num only [agent12372]
  worldRadius := (2057686099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12372]
  retainedCharge := (228805541 / 125000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1945759897 / 1000000000000 : ℝ)
  lowerTail := (450985857 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1920719657 / 200000000000 : ℝ)
  ledger := by
    have h : (296745469 / 250000000000 : ℚ) +
        (5050151171 / 500000000000000000 : ℚ) / (2057686099 / 1000000000000 : ℚ) ^ 2 +
        (228805541 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1945759897 / 1000000000000 : ℚ) + (450985857 / 200000000000 : ℚ) ≤
        (1920719657 / 200000000000 : ℚ) := by norm_num only
    have hc : (((296745469 / 250000000000 : ℚ) +
        (5050151171 / 500000000000000000 : ℚ) / (2057686099 / 1000000000000 : ℚ) ^ 2 +
        (228805541 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1945759897 / 1000000000000 : ℚ) + (450985857 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1920719657 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12372]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12372 :
    2 * 160 < 12372 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999311 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12372 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12373 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12373. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12373 : WorldParameters where
  hiddenCharge := (1186934263 / 1000000000000 : ℝ)
  frame := (63027562907 / 100000000000 : ℝ)
  moment := (5049083439 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12373 : AgentParameters :=
  { agentLedgerParameters with
    charge := (365950841 / 200000000000 : ℝ)
    frame := (744988604361 / 500000000000 : ℝ)
    root := (8728880729 / 1000000000000 : ℝ) }

noncomputable def scalar12373 : ScalarCertificate 12373 world12373 agent12373 where
  dimensionLo := 12373
  dimensionHi := 12373
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2058036199 / 1000000000000 : ℝ)
  frameLo := (63027562907 / 100000000000 : ℝ)
  frameHi := (744988604361 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12373]
  agentFrame_pos := by norm_num only [agent12373]
  worldRadius := (2058036199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12373]
  retainedCharge := (365950841 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (972025107 / 500000000000 : ℝ)
  lowerTail := (1126543877 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9597993617 / 1000000000000 : ℝ)
  ledger := by
    have h : (1186934263 / 1000000000000 : ℚ) +
        (5049083439 / 500000000000000000 : ℚ) / (2058036199 / 1000000000000 : ℚ) ^ 2 +
        (365950841 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (972025107 / 500000000000 : ℚ) + (1126543877 / 500000000000 : ℚ) ≤
        (9597993617 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1186934263 / 1000000000000 : ℚ) +
        (5049083439 / 500000000000000000 : ℚ) / (2058036199 / 1000000000000 : ℚ) ^ 2 +
        (365950841 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (972025107 / 500000000000 : ℚ) + (1126543877 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9597993617 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12373]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12373 :
    2 * 160 < 12373 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999873 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12373 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12374 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12374. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12374 : WorldParameters where
  hiddenCharge := (1186886663 / 1000000000000 : ℝ)
  frame := (630261029059 / 1000000000000 : ℝ)
  moment := (2019206409 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12374 : AgentParameters :=
  { agentLedgerParameters with
    charge := (914532349 / 500000000000 : ℝ)
    frame := (744970407873 / 500000000000 : ℝ)
    root := (8728132171 / 1000000000000 : ℝ) }

noncomputable def scalar12374 : ScalarCertificate 12374 world12374 agent12374 where
  dimensionLo := 12374
  dimensionHi := 12374
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2058386299 / 1000000000000 : ℝ)
  frameLo := (630261029059 / 1000000000000 : ℝ)
  frameHi := (744970407873 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12374]
  agentFrame_pos := by norm_num only [agent12374]
  worldRadius := (2058386299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12374]
  retainedCharge := (914532349 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (971171203 / 500000000000 : ℝ)
  lowerTail := (2251248137 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4796197137 / 500000000000 : ℝ)
  ledger := by
    have h : (1186886663 / 1000000000000 : ℚ) +
        (2019206409 / 200000000000000000 : ℚ) / (2058386299 / 1000000000000 : ℚ) ^ 2 +
        (914532349 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (971171203 / 500000000000 : ℚ) + (2251248137 / 1000000000000 : ℚ) ≤
        (4796197137 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1186886663 / 1000000000000 : ℚ) +
        (2019206409 / 200000000000000000 : ℚ) / (2058386299 / 1000000000000 : ℚ) ^ 2 +
        (914532349 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (971171203 / 500000000000 : ℚ) + (2251248137 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4796197137 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12374]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12374 :
    2 * 160 < 12374 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999099 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12374 {← IO.monoMsNow}" : IO Unit)
