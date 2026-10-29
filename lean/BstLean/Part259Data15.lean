import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12300 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12300. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12300 : WorldParameters where
  hiddenCharge := (1190444319 / 1000000000000 : ℝ)
  frame := (3156740017 / 5000000000 : ℝ)
  moment := (10255729081 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12300 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1854873123 / 1000000000000 : ℝ)
    frame := (1456968035457 / 1000000000000 : ℝ)
    root := (2198648693 / 250000000000 : ℝ) }

noncomputable def scalar12300 : ScalarCertificate 12300 world12300 agent12300 where
  dimensionLo := 12300
  dimensionHi := 12300
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2075069499 / 1000000000000 : ℝ)
  frameLo := (3156740017 / 5000000000 : ℝ)
  frameHi := (1456968035457 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12300]
  agentFrame_pos := by norm_num only [agent12300]
  worldRadius := (2075069499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12300]
  retainedCharge := (1854873123 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1927490509 / 1000000000000 : ℝ)
  lowerTail := (2207045239 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9561632001 / 1000000000000 : ℝ)
  ledger := by
    have h : (1190444319 / 1000000000000 : ℚ) +
        (10255729081 / 1000000000000000000 : ℚ) / (2075069499 / 1000000000000 : ℚ) ^ 2 +
        (1854873123 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1927490509 / 1000000000000 : ℚ) + (2207045239 / 1000000000000 : ℚ) ≤
        (9561632001 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1190444319 / 1000000000000 : ℚ) +
        (10255729081 / 1000000000000000000 : ℚ) / (2075069499 / 1000000000000 : ℚ) ^ 2 +
        (1854873123 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1927490509 / 1000000000000 : ℚ) + (2207045239 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9561632001 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12300]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12300 :
    2 * 160 < 12300 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (1374999447 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12300 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12301 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12301. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12301 : WorldParameters where
  hiddenCharge := (595197881 / 500000000000 : ℝ)
  frame := (631333225159 / 1000000000000 : ℝ)
  moment := (2050709513 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12301 : AgentParameters :=
  { agentLedgerParameters with
    charge := (370831933 / 200000000000 : ℝ)
    frame := (1456927554563 / 1000000000000 : ℝ)
    root := (274808339 / 31250000000 : ℝ) }

noncomputable def scalar12301 : ScalarCertificate 12301 world12301 agent12301 where
  dimensionLo := 12301
  dimensionHi := 12301
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2075425199 / 1000000000000 : ℝ)
  frameLo := (631333225159 / 1000000000000 : ℝ)
  frameHi := (1456927554563 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12301]
  agentFrame_pos := by norm_num only [agent12301]
  worldRadius := (2075425199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12301]
  retainedCharge := (370831933 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (962894007 / 500000000000 : ℝ)
  lowerTail := (1102611883 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9556023219 / 1000000000000 : ℝ)
  ledger := by
    have h : (595197881 / 500000000000 : ℚ) +
        (2050709513 / 200000000000000000 : ℚ) / (2075425199 / 1000000000000 : ℚ) ^ 2 +
        (370831933 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (962894007 / 500000000000 : ℚ) + (1102611883 / 500000000000 : ℚ) ≤
        (9556023219 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((595197881 / 500000000000 : ℚ) +
        (2050709513 / 200000000000000000 : ℚ) / (2075425199 / 1000000000000 : ℚ) ^ 2 +
        (370831933 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (962894007 / 500000000000 : ℚ) + (1102611883 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9556023219 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12301]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12301 :
    2 * 160 < 12301 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999996441 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12301 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12302 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12302. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12302 : WorldParameters where
  hiddenCharge := (595173609 / 500000000000 : ℝ)
  frame := (631318449383 / 1000000000000 : ℝ)
  moment := (10251366697 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12302 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1853446849 / 1000000000000 : ℝ)
    frame := (728443547041 / 500000000000 : ℝ)
    root := (351725569 / 40000000000 : ℝ) }

noncomputable def scalar12302 : ScalarCertificate 12302 world12302 agent12302 where
  dimensionLo := 12302
  dimensionHi := 12302
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2075780899 / 1000000000000 : ℝ)
  frameLo := (631318449383 / 1000000000000 : ℝ)
  frameHi := (728443547041 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12302]
  agentFrame_pos := by norm_num only [agent12302]
  worldRadius := (2075780899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12302]
  retainedCharge := (1853446849 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1924087319 / 1000000000000 : ℝ)
  lowerTail := (1101702057 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9550419631 / 1000000000000 : ℝ)
  ledger := by
    have h : (595173609 / 500000000000 : ℚ) +
        (10251366697 / 1000000000000000000 : ℚ) / (2075780899 / 1000000000000 : ℚ) ^ 2 +
        (1853446849 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1924087319 / 1000000000000 : ℚ) + (1101702057 / 500000000000 : ℚ) ≤
        (9550419631 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((595173609 / 500000000000 : ℚ) +
        (10251366697 / 1000000000000000000 : ℚ) / (2075780899 / 1000000000000 : ℚ) ^ 2 +
        (1853446849 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1924087319 / 1000000000000 : ℚ) + (1101702057 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9550419631 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12302]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12302 :
    2 * 160 < 12302 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995599 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12302 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12303 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12303. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12303 : WorldParameters where
  hiddenCharge := (18598417 / 15625000000 : ℝ)
  frame := (631303676071 / 1000000000000 : ℝ)
  moment := (5124593239 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12303 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1852734673 / 1000000000000 : ℝ)
    frame := (1456846648139 / 1000000000000 : ℝ)
    root := (8792411753 / 1000000000000 : ℝ) }

noncomputable def scalar12303 : ScalarCertificate 12303 world12303 agent12303 where
  dimensionLo := 12303
  dimensionHi := 12303
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2076136499 / 1000000000000 : ℝ)
  frameLo := (631303676071 / 1000000000000 : ℝ)
  frameHi := (1456846648139 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12303]
  agentFrame_pos := by norm_num only [agent12303]
  worldRadius := (2076136499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12303]
  retainedCharge := (1852734673 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1922388117 / 1000000000000 : ℝ)
  lowerTail := (2201585967 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9544820839 / 1000000000000 : ℝ)
  ledger := by
    have h : (18598417 / 15625000000 : ℚ) +
        (5124593239 / 500000000000000000 : ℚ) / (2076136499 / 1000000000000 : ℚ) ^ 2 +
        (1852734673 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1922388117 / 1000000000000 : ℚ) + (2201585967 / 1000000000000 : ℚ) ≤
        (9544820839 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((18598417 / 15625000000 : ℚ) +
        (5124593239 / 500000000000000000 : ℚ) / (2076136499 / 1000000000000 : ℚ) ^ 2 +
        (1852734673 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1922388117 / 1000000000000 : ℚ) + (2201585967 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9544820839 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12303]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12303 :
    2 * 160 < 12303 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999999043 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12303 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12304 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12304. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12304 : WorldParameters where
  hiddenCharge := (119025017 / 100000000000 : ℝ)
  frame := (315644452611 / 500000000000 : ℝ)
  moment := (5123503453 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12304 : AgentParameters :=
  { agentLedgerParameters with
    charge := (57875723 / 31250000000 : ℝ)
    frame := (1456806228457 / 1000000000000 : ℝ)
    root := (4395842291 / 500000000000 : ℝ) }

noncomputable def scalar12304 : ScalarCertificate 12304 world12304 agent12304 where
  dimensionLo := 12304
  dimensionHi := 12304
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2076492099 / 1000000000000 : ℝ)
  frameLo := (315644452611 / 500000000000 : ℝ)
  frameHi := (1456806228457 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12304]
  agentFrame_pos := by norm_num only [agent12304]
  worldRadius := (2076492099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12304]
  retainedCharge := (57875723 / 31250000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (960345373 / 500000000000 : ℝ)
  lowerTail := (549942419 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1192403413 / 125000000000 : ℝ)
  ledger := by
    have h : (119025017 / 100000000000 : ℚ) +
        (5123503453 / 500000000000000000 : ℚ) / (2076492099 / 1000000000000 : ℚ) ^ 2 +
        (57875723 / 31250000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (960345373 / 500000000000 : ℚ) + (549942419 / 250000000000 : ℚ) ≤
        (1192403413 / 125000000000 : ℚ) := by norm_num only
    have hc : (((119025017 / 100000000000 : ℚ) +
        (5123503453 / 500000000000000000 : ℚ) / (2076492099 / 1000000000000 : ℚ) ^ 2 +
        (57875723 / 31250000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (960345373 / 500000000000 : ℚ) + (549942419 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1192403413 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12304]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12304 :
    2 * 160 < 12304 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (687499669 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12304 {← IO.monoMsNow}" : IO Unit)
