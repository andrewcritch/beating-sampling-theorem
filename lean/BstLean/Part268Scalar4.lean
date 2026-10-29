import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12450 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12450. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12450 : WorldParameters where
  hiddenCharge := (1183306627 / 1000000000000 : ℝ)
  frame := (314579227993 / 500000000000 : ℝ)
  moment := (9935612363 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12450 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1486546289337 / 1000000000000 : ℝ)
    root := (4335972177 / 500000000000 : ℝ) }

noncomputable def scalar12450 : ScalarCertificate 12450 world12450 agent12450 where
  dimensionLo := 12450
  dimensionHi := 12450
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2085893399 / 1000000000000 : ℝ)
  frameLo := (314579227993 / 500000000000 : ℝ)
  frameHi := (1486546289337 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12450]
  agentFrame_pos := by norm_num only [agent12450]
  worldRadius := (2085893399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12450]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (907393133 / 500000000000 : ℝ)
  lowerTail := (1056519161 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9193826653 / 1000000000000 : ℝ)
  ledger := by
    have h : (1183306627 / 1000000000000 : ℚ) +
        (9935612363 / 1000000000000000000 : ℚ) / (2085893399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (907393133 / 500000000000 : ℚ) + (1056519161 / 500000000000 : ℚ) ≤
        (9193826653 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1183306627 / 1000000000000 : ℚ) +
        (9935612363 / 1000000000000000000 : ℚ) / (2085893399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (907393133 / 500000000000 : ℚ) + (1056519161 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9193826653 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12450]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12450 :
    2 * 160 < 12450 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997897 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12450 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12451 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12451. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12451 : WorldParameters where
  hiddenCharge := (1183260011 / 1000000000000 : ℝ)
  frame := (125828808057 / 200000000000 : ℝ)
  moment := (9933525391 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12451 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (297302244559 / 200000000000 : ℝ)
    root := (8671214213 / 1000000000000 : ℝ) }

noncomputable def scalar12451 : ScalarCertificate 12451 world12451 agent12451 where
  dimensionLo := 12451
  dimensionHi := 12451
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2086244399 / 1000000000000 : ℝ)
  frameLo := (125828808057 / 200000000000 : ℝ)
  frameHi := (297302244559 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12451]
  agentFrame_pos := by norm_num only [agent12451]
  worldRadius := (2086244399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12451]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1813208321 / 1000000000000 : ℝ)
  lowerTail := (2111331057 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9189247003 / 1000000000000 : ℝ)
  ledger := by
    have h : (1183260011 / 1000000000000 : ℚ) +
        (9933525391 / 1000000000000000000 : ℚ) / (2086244399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1813208321 / 1000000000000 : ℚ) + (2111331057 / 1000000000000 : ℚ) ≤
        (9189247003 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1183260011 / 1000000000000 : ℚ) +
        (9933525391 / 1000000000000000000 : ℚ) / (2086244399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1813208321 / 1000000000000 : ℚ) + (2111331057 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9189247003 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12451]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12451 :
    2 * 160 < 12451 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995303 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12451 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12452 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12452. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12452 : WorldParameters where
  hiddenCharge := (1183213407 / 1000000000000 : ℝ)
  frame := (629129626953 / 1000000000000 : ℝ)
  moment := (9931439031 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12452 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1486476173167 / 1000000000000 : ℝ)
    root := (1734096847 / 200000000000 : ℝ) }

noncomputable def scalar12452 : ScalarCertificate 12452 world12452 agent12452 where
  dimensionLo := 12452
  dimensionHi := 12452
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2086595399 / 1000000000000 : ℝ)
  frameLo := (629129626953 / 1000000000000 : ℝ)
  frameHi := (1486476173167 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12452]
  agentFrame_pos := by norm_num only [agent12452]
  worldRadius := (2086595399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12452]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1811631879 / 1000000000000 : ℝ)
  lowerTail := (84385013 / 40000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2296167813 / 250000000000 : ℝ)
  ledger := by
    have h : (1183213407 / 1000000000000 : ℚ) +
        (9931439031 / 1000000000000000000 : ℚ) / (2086595399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1811631879 / 1000000000000 : ℚ) + (84385013 / 40000000000 : ℚ) ≤
        (2296167813 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1183213407 / 1000000000000 : ℚ) +
        (9931439031 / 1000000000000000000 : ℚ) / (2086595399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1811631879 / 1000000000000 : ℚ) + (84385013 / 40000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2296167813 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12452]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12452 :
    2 * 160 < 12452 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999251 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12452 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12453 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12453. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12453 : WorldParameters where
  hiddenCharge := (36973963 / 31250000000 : ℝ)
  frame := (62911521599 / 100000000000 : ℝ)
  moment := (9929353283 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12453 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1486441146419 / 1000000000000 : ℝ)
    root := (4334877281 / 500000000000 : ℝ) }

noncomputable def scalar12453 : ScalarCertificate 12453 world12453 agent12453 where
  dimensionLo := 12453
  dimensionHi := 12453
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2086946399 / 1000000000000 : ℝ)
  frameLo := (62911521599 / 100000000000 : ℝ)
  frameHi := (1486441146419 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12453]
  agentFrame_pos := by norm_num only [agent12453]
  worldRadius := (2086946399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12453]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (362011423 / 200000000000 : ℝ)
  lowerTail := (2107921307 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2295024939 / 250000000000 : ℝ)
  ledger := by
    have h : (36973963 / 31250000000 : ℚ) +
        (9929353283 / 1000000000000000000 : ℚ) / (2086946399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (362011423 / 200000000000 : ℚ) + (2107921307 / 1000000000000 : ℚ) ≤
        (2295024939 / 250000000000 : ℚ) := by norm_num only
    have hc : (((36973963 / 31250000000 : ℚ) +
        (9929353283 / 1000000000000000000 : ℚ) / (2086946399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (362011423 / 200000000000 : ℚ) + (2107921307 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2295024939 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12453]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12453 :
    2 * 160 < 12453 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999819 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12453 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12454 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12454. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12454 : WorldParameters where
  hiddenCharge := (1183120237 / 1000000000000 : ℝ)
  frame := (125820161479 / 200000000000 : ℝ)
  moment := (9927268147 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12454 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (743203071267 / 500000000000 : ℝ)
    root := (2167256263 / 250000000000 : ℝ) }

noncomputable def scalar12454 : ScalarCertificate 12454 world12454 agent12454 where
  dimensionLo := 12454
  dimensionHi := 12454
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2087297399 / 1000000000000 : ℝ)
  frameLo := (125820161479 / 200000000000 : ℝ)
  frameHi := (743203071267 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12454]
  agentFrame_pos := by norm_num only [agent12454]
  worldRadius := (2087297399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12454]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1808483881 / 1000000000000 : ℝ)
  lowerTail := (2106218857 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9175532221 / 1000000000000 : ℝ)
  ledger := by
    have h : (1183120237 / 1000000000000 : ℚ) +
        (9927268147 / 1000000000000000000 : ℚ) / (2087297399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1808483881 / 1000000000000 : ℚ) + (2106218857 / 1000000000000 : ℚ) ≤
        (9175532221 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1183120237 / 1000000000000 : ℚ) +
        (9927268147 / 1000000000000000000 : ℚ) / (2087297399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1808483881 / 1000000000000 : ℚ) + (2106218857 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9175532221 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12454]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12454 :
    2 * 160 < 12454 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998799 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12454 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12455 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12455. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12455 : WorldParameters where
  hiddenCharge := (1183073671 / 1000000000000 : ℝ)
  frame := (629086401167 / 1000000000000 : ℝ)
  moment := (9925183623 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12455 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (29727421557 / 20000000000 : ℝ)
    root := (1733659169 / 200000000000 : ℝ) }

noncomputable def scalar12455 : ScalarCertificate 12455 world12455 agent12455 where
  dimensionLo := 12455
  dimensionHi := 12455
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2087648499 / 1000000000000 : ℝ)
  frameLo := (629086401167 / 1000000000000 : ℝ)
  frameHi := (29727421557 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12455]
  agentFrame_pos := by norm_num only [agent12455]
  worldRadius := (2087648499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12455]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (112931999 / 62500000000 : ℝ)
  lowerTail := (2104517691 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (183419359 / 20000000000 : ℝ)
  ledger := by
    have h : (1183073671 / 1000000000000 : ℚ) +
        (9925183623 / 1000000000000000000 : ℚ) / (2087648499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (112931999 / 62500000000 : ℚ) + (2104517691 / 1000000000000 : ℚ) ≤
        (183419359 / 20000000000 : ℚ) := by norm_num only
    have hc : (((1183073671 / 1000000000000 : ℚ) +
        (9925183623 / 1000000000000000000 : ℚ) / (2087648499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (112931999 / 62500000000 : ℚ) + (2104517691 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((183419359 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12455]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12455 :
    2 * 160 < 12455 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999563 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12455 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12456 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12456. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12456 : WorldParameters where
  hiddenCharge := (591513559 / 500000000000 : ℝ)
  frame := (314535998653 / 500000000000 : ℝ)
  moment := (9923099711 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12456 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (743167889543 / 500000000000 : ℝ)
    root := (1083445859 / 125000000000 : ℝ) }

noncomputable def scalar12456 : ScalarCertificate 12456 world12456 agent12456 where
  dimensionLo := 12456
  dimensionHi := 12456
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2087999899 / 1000000000000 : ℝ)
  frameLo := (314535998653 / 500000000000 : ℝ)
  frameHi := (743167889543 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12456]
  agentFrame_pos := by norm_num only [agent12456]
  worldRadius := (2087999899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12456]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (451335161 / 250000000000 : ℝ)
  lowerTail := (2102816847 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2291601191 / 250000000000 : ℝ)
  ledger := by
    have h : (591513559 / 500000000000 : ℚ) +
        (9923099711 / 1000000000000000000 : ℚ) / (2087999899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (451335161 / 250000000000 : ℚ) + (2102816847 / 1000000000000 : ℚ) ≤
        (2291601191 / 250000000000 : ℚ) := by norm_num only
    have hc : (((591513559 / 500000000000 : ℚ) +
        (9923099711 / 1000000000000000000 : ℚ) / (2087999899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (451335161 / 250000000000 : ℚ) + (2102816847 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2291601191 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12456]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12456 :
    2 * 160 < 12456 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999207 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12456 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12457 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12457. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12457 : WorldParameters where
  hiddenCharge := (1182980577 / 1000000000000 : ℝ)
  frame := (629057595811 / 1000000000000 : ℝ)
  moment := (9921016409 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12457 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (371575125793 / 250000000000 : ℝ)
    root := (4333419031 / 500000000000 : ℝ) }

noncomputable def scalar12457 : ScalarCertificate 12457 world12457 agent12457 where
  dimensionLo := 12457
  dimensionHi := 12457
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2088351399 / 1000000000000 : ℝ)
  frameLo := (629057595811 / 1000000000000 : ℝ)
  frameHi := (371575125793 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12457]
  agentFrame_pos := by norm_num only [agent12457]
  worldRadius := (2088351399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12457]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (225471367 / 125000000000 : ℝ)
  lowerTail := (26263971 / 12500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9161845531 / 1000000000000 : ℝ)
  ledger := by
    have h : (1182980577 / 1000000000000 : ℚ) +
        (9921016409 / 1000000000000000000 : ℚ) / (2088351399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (225471367 / 125000000000 : ℚ) + (26263971 / 12500000000 : ℚ) ≤
        (9161845531 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1182980577 / 1000000000000 : ℚ) +
        (9921016409 / 1000000000000000000 : ℚ) / (2088351399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (225471367 / 125000000000 : ℚ) + (26263971 / 12500000000 : ℚ) : ℚ) : ℝ) ≤
        ((9161845531 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12457]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12457 :
    2 * 160 < 12457 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499996989 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12457 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12458 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12458. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12458 : WorldParameters where
  hiddenCharge := (1182934049 / 1000000000000 : ℝ)
  frame := (314521598341 / 500000000000 : ℝ)
  moment := (9918933719 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12458 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (37156631103 / 25000000000 : ℝ)
    root := (1733221911 / 200000000000 : ℝ) }

noncomputable def scalar12458 : ScalarCertificate 12458 world12458 agent12458 where
  dimensionLo := 12458
  dimensionHi := 12458
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2088702799 / 1000000000000 : ℝ)
  frameLo := (314521598341 / 500000000000 : ℝ)
  frameHi := (37156631103 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12458]
  agentFrame_pos := by norm_num only [agent12458]
  worldRadius := (2088702799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12458]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (901101381 / 500000000000 : ℝ)
  lowerTail := (2099420069 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2289322617 / 250000000000 : ℝ)
  ledger := by
    have h : (1182934049 / 1000000000000 : ℚ) +
        (9918933719 / 1000000000000000000 : ℚ) / (2088702799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (901101381 / 500000000000 : ℚ) + (2099420069 / 1000000000000 : ℚ) ≤
        (2289322617 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1182934049 / 1000000000000 : ℚ) +
        (9918933719 / 1000000000000000000 : ℚ) / (2088702799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (901101381 / 500000000000 : ℚ) + (2099420069 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2289322617 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12458]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12458 :
    2 * 160 < 12458 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995703 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12458 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12459 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12459. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12459 : WorldParameters where
  hiddenCharge := (1182887533 / 1000000000000 : ℝ)
  frame := (629028799917 / 1000000000000 : ℝ)
  moment := (247921291 / 25000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12459 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1486230007891 / 1000000000000 : ℝ)
    root := (866538121 / 100000000000 : ℝ) }

noncomputable def scalar12459 : ScalarCertificate 12459 world12459 agent12459 where
  dimensionLo := 12459
  dimensionHi := 12459
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2089054399 / 1000000000000 : ℝ)
  frameLo := (629028799917 / 1000000000000 : ℝ)
  frameHi := (1486230007891 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12459]
  agentFrame_pos := by norm_num only [agent12459]
  worldRadius := (2089054399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12459]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1800636321 / 1000000000000 : ℝ)
  lowerTail := (419544849 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9152739347 / 1000000000000 : ℝ)
  ledger := by
    have h : (1182887533 / 1000000000000 : ℚ) +
        (247921291 / 25000000000000000 : ℚ) / (2089054399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1800636321 / 1000000000000 : ℚ) + (419544849 / 200000000000 : ℚ) ≤
        (9152739347 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1182887533 / 1000000000000 : ℚ) +
        (247921291 / 25000000000000000 : ℚ) / (2089054399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1800636321 / 1000000000000 : ℚ) + (419544849 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9152739347 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12459]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12459 :
    2 * 160 < 12459 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995949 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12459 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12460 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12460. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12460 : WorldParameters where
  hiddenCharge := (118284103 / 100000000000 : ℝ)
  frame := (629014405517 / 1000000000000 : ℝ)
  moment := (9914770171 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12460 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (297222110211 / 200000000000 : ℝ)
    root := (8664653169 / 1000000000000 : ℝ) }

noncomputable def scalar12460 : ScalarCertificate 12460 world12460 agent12460 where
  dimensionLo := 12460
  dimensionHi := 12460
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2089514699 / 1000000000000 : ℝ)
  frameLo := (629014405517 / 1000000000000 : ℝ)
  frameHi := (297222110211 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12460]
  agentFrame_pos := by norm_num only [agent12460]
  worldRadius := (2089514699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12460]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (899370581 / 500000000000 : ℝ)
  lowerTail := (2095611507 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9147207169 / 1000000000000 : ℝ)
  ledger := by
    have h : (118284103 / 100000000000 : ℚ) +
        (9914770171 / 1000000000000000000 : ℚ) / (2089514699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (899370581 / 500000000000 : ℚ) + (2095611507 / 1000000000000 : ℚ) ≤
        (9147207169 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((118284103 / 100000000000 : ℚ) +
        (9914770171 / 1000000000000000000 : ℚ) / (2089514699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (899370581 / 500000000000 : ℚ) + (2095611507 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9147207169 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12460]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12460 :
    2 * 160 < 12460 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (171874917 / 15625000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12460 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12461 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12461. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12461 : WorldParameters where
  hiddenCharge := (1182794539 / 1000000000000 : ℝ)
  frame := (15725000337 / 25000000000 : ℝ)
  moment := (9912689313 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12461 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (185759419437 / 125000000000 : ℝ)
    root := (866392529 / 100000000000 : ℝ) }

noncomputable def scalar12461 : ScalarCertificate 12461 world12461 agent12461 where
  dimensionLo := 12461
  dimensionHi := 12461
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2089866299 / 1000000000000 : ℝ)
  frameLo := (15725000337 / 25000000000 : ℝ)
  frameHi := (185759419437 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12461]
  agentFrame_pos := by norm_num only [agent12461]
  worldRadius := (2089866299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12461]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (179717811 / 100000000000 : ℝ)
  lowerTail := (104695959 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9142664823 / 1000000000000 : ℝ)
  ledger := by
    have h : (1182794539 / 1000000000000 : ℚ) +
        (9912689313 / 1000000000000000000 : ℚ) / (2089866299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (179717811 / 100000000000 : ℚ) + (104695959 / 50000000000 : ℚ) ≤
        (9142664823 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1182794539 / 1000000000000 : ℚ) +
        (9912689313 / 1000000000000000000 : ℚ) / (2089866299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (179717811 / 100000000000 : ℚ) + (104695959 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9142664823 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12461]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12461 :
    2 * 160 < 12461 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999481 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12461 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12462 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12462. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12462 : WorldParameters where
  hiddenCharge := (1182748061 / 1000000000000 : ℝ)
  frame := (314492811903 / 500000000000 : ℝ)
  moment := (1982121813 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12462 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1486040182721 / 1000000000000 : ℝ)
    root := (4331598857 / 500000000000 : ℝ) }

noncomputable def scalar12462 : ScalarCertificate 12462 world12462 agent12462 where
  dimensionLo := 12462
  dimensionHi := 12462
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2090217899 / 1000000000000 : ℝ)
  frameLo := (314492811903 / 500000000000 : ℝ)
  frameHi := (1486040182721 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12462]
  agentFrame_pos := by norm_num only [agent12462]
  worldRadius := (2090217899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12462]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1795616721 / 1000000000000 : ℝ)
  lowerTail := (2092228553 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9138126699 / 1000000000000 : ℝ)
  ledger := by
    have h : (1182748061 / 1000000000000 : ℚ) +
        (1982121813 / 200000000000000000 : ℚ) / (2090217899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1795616721 / 1000000000000 : ℚ) + (2092228553 / 1000000000000 : ℚ) ≤
        (9138126699 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1182748061 / 1000000000000 : ℚ) +
        (1982121813 / 200000000000000000 : ℚ) / (2090217899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1795616721 / 1000000000000 : ℚ) + (2092228553 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9138126699 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12462]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12462 :
    2 * 160 < 12462 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999599 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12462 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12463 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12463. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12463 : WorldParameters where
  hiddenCharge := (295675399 / 250000000000 : ℝ)
  frame := (314485618247 / 500000000000 : ℝ)
  moment := (9908529427 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12463 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1486005032717 / 1000000000000 : ℝ)
    root := (8662470369 / 1000000000000 : ℝ) }

noncomputable def scalar12463 : ScalarCertificate 12463 world12463 agent12463 where
  dimensionLo := 12463
  dimensionHi := 12463
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2090569299 / 1000000000000 : ℝ)
  frameLo := (314485618247 / 500000000000 : ℝ)
  frameHi := (1486005032717 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12463]
  agentFrame_pos := by norm_num only [agent12463]
  worldRadius := (2090569299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12463]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (224257089 / 125000000000 : ℝ)
  lowerTail := (1045269663 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1826718529 / 200000000000 : ℝ)
  ledger := by
    have h : (295675399 / 250000000000 : ℚ) +
        (9908529427 / 1000000000000000000 : ℚ) / (2090569299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (224257089 / 125000000000 : ℚ) + (1045269663 / 500000000000 : ℚ) ≤
        (1826718529 / 200000000000 : ℚ) := by norm_num only
    have hc : (((295675399 / 250000000000 : ℚ) +
        (9908529427 / 1000000000000000000 : ℚ) / (2090569299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (224257089 / 125000000000 : ℚ) + (1045269663 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1826718529 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12463]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12463 :
    2 * 160 < 12463 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999683 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12463 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12464 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12464. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12464 : WorldParameters where
  hiddenCharge := (1182655143 / 1000000000000 : ℝ)
  frame := (125791370309 / 200000000000 : ℝ)
  moment := (4953225199 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12464 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1485969905469 / 1000000000000 : ℝ)
    root := (8661743187 / 1000000000000 : ℝ) }

noncomputable def scalar12464 : ScalarCertificate 12464 world12464 agent12464 where
  dimensionLo := 12464
  dimensionHi := 12464
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2090920799 / 1000000000000 : ℝ)
  frameLo := (125791370309 / 200000000000 : ℝ)
  frameHi := (1485969905469 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12464]
  agentFrame_pos := by norm_num only [agent12464]
  worldRadius := (2090920799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12464]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (22406229 / 12500000000 : ℝ)
  lowerTail := (2088851763 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9129062513 / 1000000000000 : ℝ)
  ledger := by
    have h : (1182655143 / 1000000000000 : ℚ) +
        (4953225199 / 500000000000000000 : ℚ) / (2090920799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (22406229 / 12500000000 : ℚ) + (2088851763 / 1000000000000 : ℚ) ≤
        (9129062513 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1182655143 / 1000000000000 : ℚ) +
        (4953225199 / 500000000000000000 : ℚ) / (2090920799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (22406229 / 12500000000 : ℚ) + (2088851763 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9129062513 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12464]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12464 :
    2 * 160 < 12464 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998149 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12464 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12465 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12465. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12465 : WorldParameters where
  hiddenCharge := (1182608703 / 1000000000000 : ℝ)
  frame := (157235617239 / 250000000000 : ℝ)
  moment := (9904371979 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12465 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (297186960193 / 200000000000 : ℝ)
    root := (8661016307 / 1000000000000 : ℝ) }

noncomputable def scalar12465 : ScalarCertificate 12465 world12465 agent12465 where
  dimensionLo := 12465
  dimensionHi := 12465
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2091272299 / 1000000000000 : ℝ)
  frameLo := (157235617239 / 250000000000 : ℝ)
  frameHi := (297186960193 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12465]
  agentFrame_pos := by norm_num only [agent12465]
  worldRadius := (2091272299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12465]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (895470793 / 500000000000 : ℝ)
  lowerTail := (417433179 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9124536589 / 1000000000000 : ℝ)
  ledger := by
    have h : (1182608703 / 1000000000000 : ℚ) +
        (9904371979 / 1000000000000000000 : ℚ) / (2091272299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (895470793 / 500000000000 : ℚ) + (417433179 / 200000000000 : ℚ) ≤
        (9124536589 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1182608703 / 1000000000000 : ℚ) +
        (9904371979 / 1000000000000000000 : ℚ) / (2091272299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (895470793 / 500000000000 : ℚ) + (417433179 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9124536589 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12465]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12465 :
    2 * 160 < 12465 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999371 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12465 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12466 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12466. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12466 : WorldParameters where
  hiddenCharge := (47302491 / 40000000000 : ℝ)
  frame := (78616011091 / 125000000000 : ℝ)
  moment := (9902294169 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12466 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1485899713219 / 1000000000000 : ℝ)
    root := (8660289589 / 1000000000000 : ℝ) }

noncomputable def scalar12466 : ScalarCertificate 12466 world12466 agent12466 where
  dimensionLo := 12466
  dimensionHi := 12466
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2091623799 / 1000000000000 : ℝ)
  frameLo := (78616011091 / 125000000000 : ℝ)
  frameHi := (1485899713219 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12466]
  agentFrame_pos := by norm_num only [agent12466]
  worldRadius := (2091623799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12466]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (178938633 / 100000000000 : ℝ)
  lowerTail := (32585649 / 15625000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2280003627 / 250000000000 : ℝ)
  ledger := by
    have h : (47302491 / 40000000000 : ℚ) +
        (9902294169 / 1000000000000000000 : ℚ) / (2091623799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (178938633 / 100000000000 : ℚ) + (32585649 / 15625000000 : ℚ) ≤
        (2280003627 / 250000000000 : ℚ) := by norm_num only
    have hc : (((47302491 / 40000000000 : ℚ) +
        (9902294169 / 1000000000000000000 : ℚ) / (2091623799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (178938633 / 100000000000 : ℚ) + (32585649 / 15625000000 : ℚ) : ℚ) : ℝ) ≤
        ((2280003627 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12466]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12466 :
    2 * 160 < 12466 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999231 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12466 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12467 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12467. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12467 : WorldParameters where
  hiddenCharge := (59125793 / 50000000000 : ℝ)
  frame := (31445685543 / 50000000000 : ℝ)
  moment := (1237527121 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12467 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1485864648191 / 1000000000000 : ℝ)
    root := (2164890793 / 250000000000 : ℝ) }

noncomputable def scalar12467 : ScalarCertificate 12467 world12467 agent12467 where
  dimensionLo := 12467
  dimensionHi := 12467
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2091975399 / 1000000000000 : ℝ)
  frameLo := (31445685543 / 50000000000 : ℝ)
  frameHi := (1485864648191 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12467]
  agentFrame_pos := by norm_num only [agent12467]
  worldRadius := (2091975399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12467]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (3491861 / 1953125000 : ℝ)
  lowerTail := (2083798979 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (569718539 / 62500000000 : ℝ)
  ledger := by
    have h : (59125793 / 50000000000 : ℚ) +
        (1237527121 / 125000000000000000 : ℚ) / (2091975399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (3491861 / 1953125000 : ℚ) + (2083798979 / 1000000000000 : ℚ) ≤
        (569718539 / 62500000000 : ℚ) := by norm_num only
    have hc : (((59125793 / 50000000000 : ℚ) +
        (1237527121 / 125000000000000000 : ℚ) / (2091975399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (3491861 / 1953125000 : ℚ) + (2083798979 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((569718539 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12467]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12467 :
    2 * 160 < 12467 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995641 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12467 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12468 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12468. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12468 : WorldParameters where
  hiddenCharge := (1182469457 / 1000000000000 : ℝ)
  frame := (628899335351 / 1000000000000 : ℝ)
  moment := (1237267547 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12468 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (185728699987 / 125000000000 : ℝ)
    root := (2164709229 / 250000000000 : ℝ) }

noncomputable def scalar12468 : ScalarCertificate 12468 world12468 agent12468 where
  dimensionLo := 12468
  dimensionHi := 12468
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2092326899 / 1000000000000 : ℝ)
  frameLo := (628899335351 / 1000000000000 : ℝ)
  frameHi := (185728699987 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12468]
  agentFrame_pos := by norm_num only [agent12468]
  worldRadius := (2092326899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12468]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (357256141 / 200000000000 : ℝ)
  lowerTail := (2082117817 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9110982577 / 1000000000000 : ℝ)
  ledger := by
    have h : (1182469457 / 1000000000000 : ℚ) +
        (1237267547 / 125000000000000000 : ℚ) / (2092326899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (357256141 / 200000000000 : ℚ) + (2082117817 / 1000000000000 : ℚ) ≤
        (9110982577 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1182469457 / 1000000000000 : ℚ) +
        (1237267547 / 125000000000000000 : ℚ) / (2092326899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (357256141 / 200000000000 : ℚ) + (2082117817 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9110982577 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12468]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12468 :
    2 * 160 < 12468 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999931 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12468 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12469 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12469. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12469 : WorldParameters where
  hiddenCharge := (1182423067 / 1000000000000 : ℝ)
  frame := (3144424811 / 5000000000 : ℝ)
  moment := (9896064393 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12469 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (297158916053 / 200000000000 : ℝ)
    root := (8658110963 / 1000000000000 : ℝ) }

noncomputable def scalar12469 : ScalarCertificate 12469 world12469 agent12469 where
  dimensionLo := 12469
  dimensionHi := 12469
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2092678399 / 1000000000000 : ℝ)
  frameLo := (3144424811 / 5000000000 : ℝ)
  frameHi := (297158916053 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12469]
  agentFrame_pos := by norm_num only [agent12469]
  worldRadius := (2092678399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12469]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (892365129 / 500000000000 : ℝ)
  lowerTail := (104021919 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9106472789 / 1000000000000 : ℝ)
  ledger := by
    have h : (1182423067 / 1000000000000 : ℚ) +
        (9896064393 / 1000000000000000000 : ℚ) / (2092678399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (892365129 / 500000000000 : ℚ) + (104021919 / 50000000000 : ℚ) ≤
        (9106472789 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1182423067 / 1000000000000 : ℚ) +
        (9896064393 / 1000000000000000000 : ℚ) / (2092678399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (892365129 / 500000000000 : ℚ) + (104021919 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9106472789 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12469]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12469 :
    2 * 160 < 12469 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995451 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12469 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12470 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12470. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12470 : WorldParameters where
  hiddenCharge := (1182376689 / 1000000000000 : ℝ)
  frame := (39304411963 / 62500000000 : ℝ)
  moment := (4946994509 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12470 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1485675458363 / 1000000000000 : ℝ)
    root := (865738517 / 100000000000 : ℝ) }

noncomputable def scalar12470 : ScalarCertificate 12470 world12470 agent12470 where
  dimensionLo := 12470
  dimensionHi := 12470
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2093139099 / 1000000000000 : ℝ)
  frameLo := (39304411963 / 62500000000 : ℝ)
  frameHi := (1485675458363 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12470]
  agentFrame_pos := by norm_num only [agent12470]
  worldRadius := (2093139099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12470]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1782854391 / 1000000000000 : ℝ)
  lowerTail := (2078345911 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1137623719 / 125000000000 : ℝ)
  ledger := by
    have h : (1182376689 / 1000000000000 : ℚ) +
        (4946994509 / 500000000000000000 : ℚ) / (2093139099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1782854391 / 1000000000000 : ℚ) + (2078345911 / 1000000000000 : ℚ) ≤
        (1137623719 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1182376689 / 1000000000000 : ℚ) +
        (4946994509 / 500000000000000000 : ℚ) / (2093139099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1782854391 / 1000000000000 : ℚ) + (2078345911 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1137623719 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12470]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12470 :
    2 * 160 < 12470 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995721 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12470 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12471 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12471. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12471 : WorldParameters where
  hiddenCharge := (295582581 / 250000000000 : ℝ)
  frame := (628856222973 / 1000000000000 : ℝ)
  moment := (9891914251 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12471 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (297128095827 / 200000000000 : ℝ)
    root := (4328329839 / 500000000000 : ℝ) }

noncomputable def scalar12471 : ScalarCertificate 12471 world12471 agent12471 where
  dimensionLo := 12471
  dimensionHi := 12471
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2093490599 / 1000000000000 : ℝ)
  frameLo := (628856222973 / 1000000000000 : ℝ)
  frameHi := (297128095827 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12471]
  agentFrame_pos := by norm_num only [agent12471]
  worldRadius := (2093490599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12471]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (890653647 / 500000000000 : ℝ)
  lowerTail := (519167483 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4548244321 / 500000000000 : ℝ)
  ledger := by
    have h : (295582581 / 250000000000 : ℚ) +
        (9891914251 / 1000000000000000000 : ℚ) / (2093490599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (890653647 / 500000000000 : ℚ) + (519167483 / 250000000000 : ℚ) ≤
        (4548244321 / 500000000000 : ℚ) := by norm_num only
    have hc : (((295582581 / 250000000000 : ℚ) +
        (9891914251 / 1000000000000000000 : ℚ) / (2093490599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (890653647 / 500000000000 : ℚ) + (519167483 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4548244321 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12471]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12471 :
    2 * 160 < 12471 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994181 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12471 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12472 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12472. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12472 : WorldParameters where
  hiddenCharge := (1182283971 / 1000000000000 : ℝ)
  frame := (125768371379 / 200000000000 : ℝ)
  moment := (2472460023 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12472 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1485605516587 / 1000000000000 : ℝ)
    root := (8655934347 / 1000000000000 : ℝ) }

noncomputable def scalar12472 : ScalarCertificate 12472 world12472 agent12472 where
  dimensionLo := 12472
  dimensionHi := 12472
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2093842199 / 1000000000000 : ℝ)
  frameLo := (125768371379 / 200000000000 : ℝ)
  frameHi := (1485605516587 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12472]
  agentFrame_pos := by norm_num only [agent12472]
  worldRadius := (2093842199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12472]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1779761769 / 1000000000000 : ℝ)
  lowerTail := (518748891 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9091991353 / 1000000000000 : ℝ)
  ledger := by
    have h : (1182283971 / 1000000000000 : ℚ) +
        (2472460023 / 250000000000000000 : ℚ) / (2093842199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1779761769 / 1000000000000 : ℚ) + (518748891 / 250000000000 : ℚ) ≤
        (9091991353 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1182283971 / 1000000000000 : ℚ) +
        (2472460023 / 250000000000000000 : ℚ) / (2093842199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1779761769 / 1000000000000 : ℚ) + (518748891 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9091991353 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12472]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12472 :
    2 * 160 < 12472 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996861 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12472 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12473 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12473. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12473 : WorldParameters where
  hiddenCharge := (1182237631 / 1000000000000 : ℝ)
  frame := (628827493173 / 1000000000000 : ℝ)
  moment := (494388327 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12473 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (37139264417 / 25000000000 : ℝ)
    root := (8655209317 / 1000000000000 : ℝ) }

noncomputable def scalar12473 : ScalarCertificate 12473 world12473 agent12473 where
  dimensionLo := 12473
  dimensionHi := 12473
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2094193799 / 1000000000000 : ℝ)
  frameLo := (628827493173 / 1000000000000 : ℝ)
  frameHi := (37139264417 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12473]
  agentFrame_pos := by norm_num only [agent12473]
  worldRadius := (2094193799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12473]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (889108943 / 500000000000 : ℝ)
  lowerTail := (16586583 / 8000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9087498233 / 1000000000000 : ℝ)
  ledger := by
    have h : (1182237631 / 1000000000000 : ℚ) +
        (494388327 / 50000000000000000 : ℚ) / (2094193799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (889108943 / 500000000000 : ℚ) + (16586583 / 8000000000 : ℚ) ≤
        (9087498233 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1182237631 / 1000000000000 : ℚ) +
        (494388327 / 50000000000000000 : ℚ) / (2094193799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (889108943 / 500000000000 : ℚ) + (16586583 / 8000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9087498233 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12473]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12473 :
    2 * 160 < 12473 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997679 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12473 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12474 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12474. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12474 : WorldParameters where
  hiddenCharge := (1182191303 / 1000000000000 : ℝ)
  frame := (628813131807 / 1000000000000 : ℝ)
  moment := (2471423399 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12474 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1485535659399 / 1000000000000 : ℝ)
    root := (270452639 / 31250000000 : ℝ) }

noncomputable def scalar12474 : ScalarCertificate 12474 world12474 agent12474 where
  dimensionLo := 12474
  dimensionHi := 12474
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2094545299 / 1000000000000 : ℝ)
  frameLo := (628813131807 / 1000000000000 : ℝ)
  frameHi := (1485535659399 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12474]
  agentFrame_pos := by norm_num only [agent12474]
  worldRadius := (2094545299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12474]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (355335079 / 200000000000 : ℝ)
  lowerTail := (258956451 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4541504497 / 500000000000 : ℝ)
  ledger := by
    have h : (1182191303 / 1000000000000 : ℚ) +
        (2471423399 / 250000000000000000 : ℚ) / (2094545299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (355335079 / 200000000000 : ℚ) + (258956451 / 125000000000 : ℚ) ≤
        (4541504497 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1182191303 / 1000000000000 : ℚ) +
        (2471423399 / 250000000000000000 : ℚ) / (2094545299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (355335079 / 200000000000 : ℚ) + (258956451 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4541504497 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12474]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12474 :
    2 * 160 < 12474 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996607 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12474 {← IO.monoMsNow}" : IO Unit)
