import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12725 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12725. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12725 : WorldParameters where
  hiddenCharge := (1170946861 / 1000000000000 : ℝ)
  frame := (125056263779 / 200000000000 : ℝ)
  moment := (938400259 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12725 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368777899897 / 250000000000 : ℝ)
    root := (66238347 / 7812500000 : ℝ) }

noncomputable def scalar12725 : ScalarCertificate 12725 world12725 agent12725 where
  dimensionLo := 12725
  dimensionHi := 12725
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2186347099 / 1000000000000 : ℝ)
  frameLo := (125056263779 / 200000000000 : ℝ)
  frameHi := (368777899897 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12725]
  agentFrame_pos := by norm_num only [agent12725]
  worldRadius := (2186347099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12725]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (142658831 / 100000000000 : ℝ)
  lowerTail := (1688385951 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1006025113 / 125000000000 : ℝ)
  ledger := by
    have h : (1170946861 / 1000000000000 : ℚ) +
        (938400259 / 100000000000000000 : ℚ) / (2186347099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (142658831 / 100000000000 : ℚ) + (1688385951 / 1000000000000 : ℚ) ≤
        (1006025113 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1170946861 / 1000000000000 : ℚ) +
        (938400259 / 100000000000000000 : ℚ) / (2186347099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (142658831 / 100000000000 : ℚ) + (1688385951 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1006025113 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12725]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12725 :
    2 * 160 < 12725 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997147 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12725 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12726 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12726. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12726 : WorldParameters where
  hiddenCharge := (1170903547 / 1000000000000 : ℝ)
  frame := (19539610377 / 31250000000 : ℝ)
  moment := (1876415141 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12726 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1475079828531 / 1000000000000 : ℝ)
    root := (8477831289 / 1000000000000 : ℝ) }

noncomputable def scalar12726 : ScalarCertificate 12726 world12726 agent12726 where
  dimensionLo := 12726
  dimensionHi := 12726
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2186704499 / 1000000000000 : ℝ)
  frameLo := (19539610377 / 31250000000 : ℝ)
  frameHi := (1475079828531 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12726]
  agentFrame_pos := by norm_num only [agent12726]
  worldRadius := (2186704499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12726]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (285076843 / 200000000000 : ℝ)
  lowerTail := (1687062681 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4022292793 / 500000000000 : ℝ)
  ledger := by
    have h : (1170903547 / 1000000000000 : ℚ) +
        (1876415141 / 200000000000000000 : ℚ) / (2186704499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (285076843 / 200000000000 : ℚ) + (1687062681 / 1000000000000 : ℚ) ≤
        (4022292793 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1170903547 / 1000000000000 : ℚ) +
        (1876415141 / 200000000000000000 : ℚ) / (2186704499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (285076843 / 200000000000 : ℚ) + (1687062681 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4022292793 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12726]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12726 :
    2 * 160 < 12726 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996843 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12726 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12727 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12727. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12727 : WorldParameters where
  hiddenCharge := (234172049 / 200000000000 : ℝ)
  frame := (625253747439 / 1000000000000 : ℝ)
  moment := (2345037343 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12727 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737524035741 / 500000000000 : ℝ)
    root := (8477154371 / 1000000000000 : ℝ) }

noncomputable def scalar12727 : ScalarCertificate 12727 world12727 agent12727 where
  dimensionLo := 12727
  dimensionHi := 12727
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2187061999 / 1000000000000 : ℝ)
  frameLo := (625253747439 / 1000000000000 : ℝ)
  frameHi := (737524035741 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12727]
  agentFrame_pos := by norm_num only [agent12727]
  worldRadius := (2187061999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12727]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1424181373 / 1000000000000 : ℝ)
  lowerTail := (1685740711 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8040973347 / 1000000000000 : ℝ)
  ledger := by
    have h : (234172049 / 200000000000 : ℚ) +
        (2345037343 / 250000000000000000 : ℚ) / (2187061999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1424181373 / 1000000000000 : ℚ) + (1685740711 / 1000000000000 : ℚ) ≤
        (8040973347 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((234172049 / 200000000000 : ℚ) +
        (2345037343 / 250000000000000000 : ℚ) / (2187061999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1424181373 / 1000000000000 : ℚ) + (1685740711 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8040973347 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12727]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12727 :
    2 * 160 < 12727 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999963 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12727 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12728 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12728. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12728 : WorldParameters where
  hiddenCharge := (585408477 / 500000000000 : ℝ)
  frame := (625239965021 / 1000000000000 : ℝ)
  moment := (1172277949 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12728 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (184377041793 / 125000000000 : ℝ)
    root := (2119119399 / 250000000000 : ℝ) }

noncomputable def scalar12728 : ScalarCertificate 12728 world12728 agent12728 where
  dimensionLo := 12728
  dimensionHi := 12728
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2187419499 / 1000000000000 : ℝ)
  frameLo := (625239965021 / 1000000000000 : ℝ)
  frameHi := (184377041793 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12728]
  agentFrame_pos := by norm_num only [agent12728]
  worldRadius := (2187419499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12728]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (284595933 / 200000000000 : ℝ)
  lowerTail := (21055249 / 12500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4018682063 / 500000000000 : ℝ)
  ledger := by
    have h : (585408477 / 500000000000 : ℚ) +
        (1172277949 / 125000000000000000 : ℚ) / (2187419499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (284595933 / 200000000000 : ℚ) + (21055249 / 12500000000 : ℚ) ≤
        (4018682063 / 500000000000 : ℚ) := by norm_num only
    have hc : (((585408477 / 500000000000 : ℚ) +
        (1172277949 / 125000000000000000 : ℚ) / (2187419499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (284595933 / 200000000000 : ℚ) + (21055249 / 12500000000 : ℚ) : ℚ) : ℝ) ≤
        ((4018682063 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12728]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12728 :
    2 * 160 < 12728 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999863 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12728 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12729 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12729. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12729 : WorldParameters where
  hiddenCharge := (585386837 / 500000000000 : ℝ)
  frame := (625226184807 / 1000000000000 : ℝ)
  moment := (1875259673 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12729 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (294996923421 / 200000000000 : ℝ)
    root := (1059475137 / 125000000000 : ℝ) }

noncomputable def scalar12729 : ScalarCertificate 12729 world12729 agent12729 where
  dimensionLo := 12729
  dimensionHi := 12729
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2187776899 / 1000000000000 : ℝ)
  frameLo := (625226184807 / 1000000000000 : ℝ)
  frameHi := (294996923421 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12729]
  agentFrame_pos := by norm_num only [agent12729]
  worldRadius := (2187776899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12729]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1421779117 / 1000000000000 : ℝ)
  lowerTail := (210387541 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2008439537 / 250000000000 : ℝ)
  ledger := by
    have h : (585386837 / 500000000000 : ℚ) +
        (1875259673 / 200000000000000000 : ℚ) / (2187776899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1421779117 / 1000000000000 : ℚ) + (210387541 / 125000000000 : ℚ) ≤
        (2008439537 / 250000000000 : ℚ) := by norm_num only
    have hc : (((585386837 / 500000000000 : ℚ) +
        (1875259673 / 200000000000000000 : ℚ) / (2187776899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1421779117 / 1000000000000 : ℚ) + (210387541 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2008439537 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12729]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12729 :
    2 * 160 < 12729 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998481 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12729 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12730 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12730. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12730 : WorldParameters where
  hiddenCharge := (585365203 / 500000000000 : ℝ)
  frame := (625212406799 / 1000000000000 : ℝ)
  moment := (937437369 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12730 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474871927429 / 1000000000000 : ℝ)
    root := (2118781201 / 250000000000 : ℝ) }

noncomputable def scalar12730 : ScalarCertificate 12730 world12730 agent12730 where
  dimensionLo := 12730
  dimensionHi := 12730
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2188247199 / 1000000000000 : ℝ)
  frameLo := (625212406799 / 1000000000000 : ℝ)
  frameHi := (1474871927429 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12730]
  agentFrame_pos := by norm_num only [agent12730]
  worldRadius := (2188247199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12730]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (177540487 / 125000000000 : ℝ)
  lowerTail := (168145193 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1605873473 / 200000000000 : ℝ)
  ledger := by
    have h : (585365203 / 500000000000 : ℚ) +
        (937437369 / 100000000000000000 : ℚ) / (2188247199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (177540487 / 125000000000 : ℚ) + (168145193 / 100000000000 : ℚ) ≤
        (1605873473 / 200000000000 : ℚ) := by norm_num only
    have hc : (((585365203 / 500000000000 : ℚ) +
        (937437369 / 100000000000000000 : ℚ) / (2188247199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (177540487 / 125000000000 : ℚ) + (168145193 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1605873473 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12730]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12730 :
    2 * 160 < 12730 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997269 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12730 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12731 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12731. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12731 : WorldParameters where
  hiddenCharge := (1170687149 / 1000000000000 : ℝ)
  frame := (125039726199 / 200000000000 : ℝ)
  moment := (4686224783 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12731 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737420122497 / 500000000000 : ℝ)
    root := (8474448721 / 1000000000000 : ℝ) }

noncomputable def scalar12731 : ScalarCertificate 12731 world12731 agent12731 where
  dimensionLo := 12731
  dimensionHi := 12731
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2188604699 / 1000000000000 : ℝ)
  frameLo := (125039726199 / 200000000000 : ℝ)
  frameHi := (737420122497 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12731]
  agentFrame_pos := by norm_num only [agent12731]
  worldRadius := (2188604699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12731]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1419125961 / 1000000000000 : ℝ)
  lowerTail := (840067539 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4012884053 / 500000000000 : ℝ)
  ledger := by
    have h : (1170687149 / 1000000000000 : ℚ) +
        (4686224783 / 500000000000000000 : ℚ) / (2188604699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1419125961 / 1000000000000 : ℚ) + (840067539 / 500000000000 : ℚ) ≤
        (4012884053 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1170687149 / 1000000000000 : ℚ) +
        (4686224783 / 500000000000000000 : ℚ) / (2188604699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1419125961 / 1000000000000 : ℚ) + (840067539 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4012884053 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12731]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12731 :
    2 * 160 < 12731 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994579 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12731 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12732 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12732. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12732 : WorldParameters where
  hiddenCharge := (18291311 / 15625000000 : ℝ)
  frame := (312592428697 / 500000000000 : ℝ)
  moment := (1874105199 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12732 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737404288261 / 500000000000 : ℝ)
    root := (423688639 / 50000000000 : ℝ) }

noncomputable def scalar12732 : ScalarCertificate 12732 world12732 agent12732 where
  dimensionLo := 12732
  dimensionHi := 12732
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2188962099 / 1000000000000 : ℝ)
  frameLo := (312592428697 / 500000000000 : ℝ)
  frameHi := (737404288261 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12732]
  agentFrame_pos := by norm_num only [agent12732]
  worldRadius := (2188962099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12732]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (283585809 / 200000000000 : ℝ)
  lowerTail := (67152771 / 40000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8022171797 / 1000000000000 : ℝ)
  ledger := by
    have h : (18291311 / 15625000000 : ℚ) +
        (1874105199 / 200000000000000000 : ℚ) / (2188962099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (283585809 / 200000000000 : ℚ) + (67152771 / 40000000000 : ℚ) ≤
        (8022171797 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((18291311 / 15625000000 : ℚ) +
        (1874105199 / 200000000000000000 : ℚ) / (2188962099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (283585809 / 200000000000 : ℚ) + (67152771 / 40000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8022171797 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12732]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12732 :
    2 * 160 < 12732 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998763 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12732 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12733 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12733. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12733 : WorldParameters where
  hiddenCharge := (117060067 / 100000000000 : ℝ)
  frame := (156292771499 / 250000000000 : ℝ)
  moment := (374744119 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12733 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737388461001 / 500000000000 : ℝ)
    root := (4236548557 / 500000000000 : ℝ) }

noncomputable def scalar12733 : ScalarCertificate 12733 world12733 agent12733 where
  dimensionLo := 12733
  dimensionHi := 12733
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2189319599 / 1000000000000 : ℝ)
  frameLo := (156292771499 / 250000000000 : ℝ)
  frameHi := (737388461001 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12733]
  agentFrame_pos := by norm_num only [agent12733]
  worldRadius := (2189319599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12733]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1416733429 / 1000000000000 : ℝ)
  lowerTail := (83875241 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4009289329 / 500000000000 : ℝ)
  ledger := by
    have h : (117060067 / 100000000000 : ℚ) +
        (374744119 / 40000000000000000 : ℚ) / (2189319599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1416733429 / 1000000000000 : ℚ) + (83875241 / 50000000000 : ℚ) ≤
        (4009289329 / 500000000000 : ℚ) := by norm_num only
    have hc : (((117060067 / 100000000000 : ℚ) +
        (374744119 / 40000000000000000 : ℚ) / (2189319599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1416733429 / 1000000000000 : ℚ) + (83875241 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4009289329 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12733]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12733 :
    2 * 160 < 12733 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999667 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12733 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12734 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12734. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12734 : WorldParameters where
  hiddenCharge := (146319681 / 125000000000 : ℝ)
  frame := (625157316801 / 1000000000000 : ℝ)
  moment := (9366680507 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12734 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (294949057467 / 200000000000 : ℝ)
    root := (1059052707 / 125000000000 : ℝ) }

noncomputable def scalar12734 : ScalarCertificate 12734 world12734 agent12734 where
  dimensionLo := 12734
  dimensionHi := 12734
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2189677199 / 1000000000000 : ℝ)
  frameLo := (625157316801 / 1000000000000 : ℝ)
  frameHi := (294949057467 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12734]
  agentFrame_pos := by norm_num only [agent12734]
  worldRadius := (2189677199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12734]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (35388477 / 25000000000 : ℝ)
  lowerTail := (838095843 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8014988631 / 1000000000000 : ℝ)
  ledger := by
    have h : (146319681 / 125000000000 : ℚ) +
        (9366680507 / 1000000000000000000 : ℚ) / (2189677199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (35388477 / 25000000000 : ℚ) + (838095843 / 500000000000 : ℚ) ≤
        (8014988631 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((146319681 / 125000000000 : ℚ) +
        (9366680507 / 1000000000000000000 : ℚ) / (2189677199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (35388477 / 25000000000 : ℚ) + (838095843 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8014988631 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12734]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12734 :
    2 * 160 < 12734 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999219 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12734 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12735 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12735. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12735 : WorldParameters where
  hiddenCharge := (1170514237 / 1000000000000 : ℝ)
  frame := (39071471863 / 62500000000 : ℝ)
  moment := (9364758589 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12735 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474713672511 / 1000000000000 : ℝ)
    root := (4235873203 / 500000000000 : ℝ) }

noncomputable def scalar12735 : ScalarCertificate 12735 world12735 agent12735 where
  dimensionLo := 12735
  dimensionHi := 12735
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2190034699 / 1000000000000 : ℝ)
  frameLo := (39071471863 / 62500000000 : ℝ)
  frameHi := (1474713672511 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12735]
  agentFrame_pos := by norm_num only [agent12735]
  worldRadius := (2190034699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12735]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1414345827 / 1000000000000 : ℝ)
  lowerTail := (837439843 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4005700857 / 500000000000 : ℝ)
  ledger := by
    have h : (1170514237 / 1000000000000 : ℚ) +
        (9364758589 / 1000000000000000000 : ℚ) / (2190034699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1414345827 / 1000000000000 : ℚ) + (837439843 / 500000000000 : ℚ) ≤
        (4005700857 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1170514237 / 1000000000000 : ℚ) +
        (9364758589 / 1000000000000000000 : ℚ) / (2190034699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1414345827 / 1000000000000 : ℚ) + (837439843 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4005700857 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12735]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12735 :
    2 * 160 < 12735 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996679 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12735 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12736 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12736. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12736 : WorldParameters where
  hiddenCharge := (1170471037 / 1000000000000 : ℝ)
  frame := (78141223127 / 125000000000 : ℝ)
  moment := (9362837223 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12736 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368670517903 / 250000000000 : ℝ)
    root := (4235535649 / 500000000000 : ℝ) }

noncomputable def scalar12736 : ScalarCertificate 12736 world12736 agent12736 where
  dimensionLo := 12736
  dimensionHi := 12736
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2190392199 / 1000000000000 : ℝ)
  frameLo := (78141223127 / 125000000000 : ℝ)
  frameHi := (368670517903 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12736]
  agentFrame_pos := by norm_num only [agent12736]
  worldRadius := (2190392199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12736]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (706576837 / 500000000000 : ℝ)
  lowerTail := (1673568823 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8007817731 / 1000000000000 : ℝ)
  ledger := by
    have h : (1170471037 / 1000000000000 : ℚ) +
        (9362837223 / 1000000000000000000 : ℚ) / (2190392199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (706576837 / 500000000000 : ℚ) + (1673568823 / 1000000000000 : ℚ) ≤
        (8007817731 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1170471037 / 1000000000000 : ℚ) +
        (9362837223 / 1000000000000000000 : ℚ) / (2190392199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (706576837 / 500000000000 : ℚ) + (1673568823 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8007817731 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12736]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12736 :
    2 * 160 < 12736 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999443 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12736 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12737 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12737. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12737 : WorldParameters where
  hiddenCharge := (1170427849 / 1000000000000 : ℝ)
  frame := (25004640897 / 40000000000 : ℝ)
  moment := (1170114551 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12737 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (737325245269 / 500000000000 : ℝ)
    root := (529399779 / 62500000000 : ℝ) }

noncomputable def scalar12737 : ScalarCertificate 12737 world12737 agent12737 where
  dimensionLo := 12737
  dimensionHi := 12737
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2190749699 / 1000000000000 : ℝ)
  frameLo := (25004640897 / 40000000000 : ℝ)
  frameHi := (737325245269 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12737]
  agentFrame_pos := by norm_num only [agent12737]
  worldRadius := (2190749699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12737]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (705981377 / 500000000000 : ℝ)
  lowerTail := (836129621 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1600847393 / 200000000000 : ℝ)
  ledger := by
    have h : (1170427849 / 1000000000000 : ℚ) +
        (1170114551 / 125000000000000000 : ℚ) / (2190749699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (705981377 / 500000000000 : ℚ) + (836129621 / 500000000000 : ℚ) ≤
        (1600847393 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1170427849 / 1000000000000 : ℚ) +
        (1170114551 / 125000000000000000 : ℚ) / (2190749699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (705981377 / 500000000000 : ℚ) + (836129621 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1600847393 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12737]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12737 :
    2 * 160 < 12737 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997307 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12737 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12738 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12738. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12738 : WorldParameters where
  hiddenCharge := (1170384673 / 1000000000000 : ℝ)
  frame := (125020452407 / 200000000000 : ℝ)
  moment := (9358996143 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12738 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474618923371 / 1000000000000 : ℝ)
    root := (8469721837 / 1000000000000 : ℝ) }

noncomputable def scalar12738 : ScalarCertificate 12738 world12738 agent12738 where
  dimensionLo := 12738
  dimensionHi := 12738
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2191107299 / 1000000000000 : ℝ)
  frameLo := (125020452407 / 200000000000 : ℝ)
  frameHi := (1474618923371 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12738]
  agentFrame_pos := by norm_num only [agent12738]
  worldRadius := (2191107299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12738]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1410773071 / 1000000000000 : ℝ)
  lowerTail := (52217217 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (200016481 / 25000000000 : ℝ)
  ledger := by
    have h : (1170384673 / 1000000000000 : ℚ) +
        (9358996143 / 1000000000000000000 : ℚ) / (2191107299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1410773071 / 1000000000000 : ℚ) + (52217217 / 31250000000 : ℚ) ≤
        (200016481 / 25000000000 : ℚ) := by norm_num only
    have hc : (((1170384673 / 1000000000000 : ℚ) +
        (9358996143 / 1000000000000000000 : ℚ) / (2191107299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1410773071 / 1000000000000 : ℚ) + (52217217 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((200016481 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12738]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12738 :
    2 * 160 < 12738 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999009 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12738 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12739 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12739. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12739 : WorldParameters where
  hiddenCharge := (1170341507 / 1000000000000 : ℝ)
  frame := (156272125961 / 250000000000 : ℝ)
  moment := (2339269107 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12739 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474587080643 / 1000000000000 : ℝ)
    root := (4234523709 / 500000000000 : ℝ) }

noncomputable def scalar12739 : ScalarCertificate 12739 world12739 agent12739 where
  dimensionLo := 12739
  dimensionHi := 12739
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2191465199 / 1000000000000 : ℝ)
  frameLo := (156272125961 / 250000000000 : ℝ)
  frameHi := (1474587080643 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12739]
  agentFrame_pos := by norm_num only [agent12739]
  worldRadius := (2191465199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12739]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (704791771 / 500000000000 : ℝ)
  lowerTail := (208705321 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3998540877 / 500000000000 : ℝ)
  ledger := by
    have h : (1170341507 / 1000000000000 : ℚ) +
        (2339269107 / 250000000000000000 : ℚ) / (2191465199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (704791771 / 500000000000 : ℚ) + (208705321 / 125000000000 : ℚ) ≤
        (3998540877 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1170341507 / 1000000000000 : ℚ) +
        (2339269107 / 250000000000000000 : ℚ) / (2191465199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (704791771 / 500000000000 : ℚ) + (208705321 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3998540877 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12739]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12739 :
    2 * 160 < 12739 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998527 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12739 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12740 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12740. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12740 : WorldParameters where
  hiddenCharge := (1170298353 / 1000000000000 : ℝ)
  frame := (156268686963 / 250000000000 : ℝ)
  moment := (584697329 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12740 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (46077323701 / 31250000000 : ℝ)
    root := (8468373139 / 1000000000000 : ℝ) }

noncomputable def scalar12740 : ScalarCertificate 12740 world12740 agent12740 where
  dimensionLo := 12740
  dimensionHi := 12740
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2191936099 / 1000000000000 : ℝ)
  frameLo := (156268686963 / 250000000000 : ℝ)
  frameHi := (46077323701 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12740]
  agentFrame_pos := by norm_num only [agent12740]
  worldRadius := (2191936099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12740]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (704070759 / 500000000000 : ℝ)
  lowerTail := (1668008013 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (99909069 / 12500000000 : ℝ)
  ledger := by
    have h : (1170298353 / 1000000000000 : ℚ) +
        (584697329 / 62500000000000000 : ℚ) / (2191936099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (704070759 / 500000000000 : ℚ) + (1668008013 / 1000000000000 : ℚ) ≤
        (99909069 / 12500000000 : ℚ) := by norm_num only
    have hc : (((1170298353 / 1000000000000 : ℚ) +
        (584697329 / 62500000000000000 : ℚ) / (2191936099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (704070759 / 500000000000 : ℚ) + (1668008013 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((99909069 / 12500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12740]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12740 :
    2 * 160 < 12740 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997077 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12740 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12741 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12741. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12741 : WorldParameters where
  hiddenCharge := (1170255211 / 1000000000000 : ℝ)
  frame := (625060994059 / 1000000000000 : ℝ)
  moment := (187064773 / 20000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12741 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368610628733 / 250000000000 : ℝ)
    root := (1693539827 / 200000000000 : ℝ) }

noncomputable def scalar12741 : ScalarCertificate 12741 world12741 agent12741 where
  dimensionLo := 12741
  dimensionHi := 12741
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2192294099 / 1000000000000 : ℝ)
  frameLo := (625060994059 / 1000000000000 : ℝ)
  frameHi := (368610628733 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12741]
  agentFrame_pos := by norm_num only [agent12741]
  worldRadius := (2192294099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12741]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (703477211 / 500000000000 : ℝ)
  lowerTail := (1666702161 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (499322147 / 62500000000 : ℝ)
  ledger := by
    have h : (1170255211 / 1000000000000 : ℚ) +
        (187064773 / 20000000000000000 : ℚ) / (2192294099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (703477211 / 500000000000 : ℚ) + (1666702161 / 1000000000000 : ℚ) ≤
        (499322147 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1170255211 / 1000000000000 : ℚ) +
        (187064773 / 20000000000000000 : ℚ) / (2192294099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (703477211 / 500000000000 : ℚ) + (1666702161 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((499322147 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12741]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12741 :
    2 * 160 < 12741 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999871 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12741 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12742 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12742. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12742 : WorldParameters where
  hiddenCharge := (1170212079 / 1000000000000 : ℝ)
  frame := (19532726327 / 31250000000 : ℝ)
  moment := (1870264117 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12742 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474410697137 / 1000000000000 : ℝ)
    root := (8467025337 / 1000000000000 : ℝ) }

noncomputable def scalar12742 : ScalarCertificate 12742 world12742 agent12742 where
  dimensionLo := 12742
  dimensionHi := 12742
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2192652199 / 1000000000000 : ℝ)
  frameLo := (19532726327 / 31250000000 : ℝ)
  frameHi := (1474410697137 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12742]
  agentFrame_pos := by norm_num only [agent12742]
  worldRadius := (2192652199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12742]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (140576861 / 100000000000 : ℝ)
  lowerTail := (832698827 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7985586331 / 1000000000000 : ℝ)
  ledger := by
    have h : (1170212079 / 1000000000000 : ℚ) +
        (1870264117 / 200000000000000000 : ℚ) / (2192652199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (140576861 / 100000000000 : ℚ) + (832698827 / 500000000000 : ℚ) ≤
        (7985586331 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1170212079 / 1000000000000 : ℚ) +
        (1870264117 / 200000000000000000 : ℚ) / (2192652199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (140576861 / 100000000000 : ℚ) + (832698827 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7985586331 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12742]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12742 :
    2 * 160 < 12742 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997287 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12742 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12743 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12743. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12743 : WorldParameters where
  hiddenCharge := (1170168959 / 1000000000000 : ℝ)
  frame := (312516746533 / 500000000000 : ℝ)
  moment := (9349403071 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12743 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (184297361653 / 125000000000 : ℝ)
    root := (26457349 / 3125000000 : ℝ) }

noncomputable def scalar12743 : ScalarCertificate 12743 world12743 agent12743 where
  dimensionLo := 12743
  dimensionHi := 12743
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2193010199 / 1000000000000 : ℝ)
  frameLo := (312516746533 / 500000000000 : ℝ)
  frameHi := (184297361653 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12743]
  agentFrame_pos := by norm_num only [agent12743]
  worldRadius := (2193010199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12743]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (351145951 / 250000000000 : ℝ)
  lowerTail := (1664094183 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (798202123 / 100000000000 : ℝ)
  ledger := by
    have h : (1170168959 / 1000000000000 : ℚ) +
        (9349403071 / 1000000000000000000 : ℚ) / (2193010199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (351145951 / 250000000000 : ℚ) + (1664094183 / 1000000000000 : ℚ) ≤
        (798202123 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1170168959 / 1000000000000 : ℚ) +
        (9349403071 / 1000000000000000000 : ℚ) / (2193010199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (351145951 / 250000000000 : ℚ) + (1664094183 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((798202123 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12743]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12743 :
    2 * 160 < 12743 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998621 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12743 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12744 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12744. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12744 : WorldParameters where
  hiddenCharge := (1170125851 / 1000000000000 : ℝ)
  frame := (312509872933 / 500000000000 : ℝ)
  moment := (1869497221 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12744 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (368586777273 / 250000000000 : ℝ)
    root := (1058209787 / 125000000000 : ℝ) }

noncomputable def scalar12744 : ScalarCertificate 12744 world12744 agent12744 where
  dimensionLo := 12744
  dimensionHi := 12744
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2193368199 / 1000000000000 : ℝ)
  frameLo := (312509872933 / 500000000000 : ℝ)
  frameHi := (368586777273 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12744]
  agentFrame_pos := by norm_num only [agent12744]
  worldRadius := (2193368199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12744]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (43856257 / 31250000000 : ℝ)
  lowerTail := (831395993 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (319138373 / 40000000000 : ℝ)
  ledger := by
    have h : (1170125851 / 1000000000000 : ℚ) +
        (1869497221 / 200000000000000000 : ℚ) / (2193368199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (43856257 / 31250000000 : ℚ) + (831395993 / 500000000000 : ℚ) ≤
        (319138373 / 40000000000 : ℚ) := by norm_num only
    have hc : (((1170125851 / 1000000000000 : ℚ) +
        (1869497221 / 200000000000000000 : ℚ) / (2193368199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (43856257 / 31250000000 : ℚ) + (831395993 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((319138373 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12744]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12744 :
    2 * 160 < 12744 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997723 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12744 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12745 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12745. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12745 : WorldParameters where
  hiddenCharge := (585041377 / 500000000000 : ℝ)
  frame := (625006000861 / 1000000000000 : ℝ)
  moment := (9345569689 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12745 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147431534473 / 100000000000 : ℝ)
    root := (8465005119 / 1000000000000 : ℝ) }

noncomputable def scalar12745 : ScalarCertificate 12745 world12745 agent12745 where
  dimensionLo := 12745
  dimensionHi := 12745
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2193726199 / 1000000000000 : ℝ)
  frameLo := (625006000861 / 1000000000000 : ℝ)
  frameHi := (147431534473 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12745]
  agentFrame_pos := by norm_num only [agent12745]
  worldRadius := (2193726199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12745]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (701108907 / 500000000000 : ℝ)
  lowerTail := (415372751 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (15949801 / 2000000000 : ℝ)
  ledger := by
    have h : (585041377 / 500000000000 : ℚ) +
        (9345569689 / 1000000000000000000 : ℚ) / (2193726199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (701108907 / 500000000000 : ℚ) + (415372751 / 250000000000 : ℚ) ≤
        (15949801 / 2000000000 : ℚ) := by norm_num only
    have hc : (((585041377 / 500000000000 : ℚ) +
        (9345569689 / 1000000000000000000 : ℚ) / (2193726199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (701108907 / 500000000000 : ℚ) + (415372751 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((15949801 / 2000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12745]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12745 :
    2 * 160 < 12745 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997283 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12745 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12746 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12746. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12746 : WorldParameters where
  hiddenCharge := (292509917 / 250000000000 : ℝ)
  frame := (156248064513 / 250000000000 : ℝ)
  moment := (4671826911 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12746 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474283594223 / 1000000000000 : ℝ)
    root := (8464332081 / 1000000000000 : ℝ) }

noncomputable def scalar12746 : ScalarCertificate 12746 world12746 agent12746 where
  dimensionLo := 12746
  dimensionHi := 12746
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2194084299 / 1000000000000 : ℝ)
  frameLo := (156248064513 / 250000000000 : ℝ)
  frameHi := (1474283594223 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12746]
  agentFrame_pos := by norm_num only [agent12746]
  worldRadius := (2194084299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12746]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (56041463 / 40000000000 : ℝ)
  lowerTail := (41504781 / 25000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (996418073 / 125000000000 : ℝ)
  ledger := by
    have h : (292509917 / 250000000000 : ℚ) +
        (4671826911 / 500000000000000000 : ℚ) / (2194084299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (56041463 / 40000000000 : ℚ) + (41504781 / 25000000000 : ℚ) ≤
        (996418073 / 125000000000 : ℚ) := by norm_num only
    have hc : (((292509917 / 250000000000 : ℚ) +
        (4671826911 / 500000000000000000 : ℚ) / (2194084299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (56041463 / 40000000000 : ℚ) + (41504781 / 25000000000 : ℚ) : ℚ) : ℝ) ≤
        ((996418073 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12746]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12746 :
    2 * 160 < 12746 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999407 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12746 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12747 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12747. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12747 : WorldParameters where
  hiddenCharge := (584998297 / 500000000000 : ℝ)
  frame := (624978517439 / 1000000000000 : ℝ)
  moment := (9341738503 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12747 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1474251857563 / 1000000000000 : ℝ)
    root := (8463659317 / 1000000000000 : ℝ) }

noncomputable def scalar12747 : ScalarCertificate 12747 world12747 agent12747 where
  dimensionLo := 12747
  dimensionHi := 12747
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2194442299 / 1000000000000 : ℝ)
  frameLo := (624978517439 / 1000000000000 : ℝ)
  frameHi := (1474251857563 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12747]
  agentFrame_pos := by norm_num only [agent12747]
  worldRadius := (2194442299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12747]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1399856449 / 1000000000000 : ℝ)
  lowerTail := (829446311 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3983895899 / 500000000000 : ℝ)
  ledger := by
    have h : (584998297 / 500000000000 : ℚ) +
        (9341738503 / 1000000000000000000 : ℚ) / (2194442299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1399856449 / 1000000000000 : ℚ) + (829446311 / 500000000000 : ℚ) ≤
        (3983895899 / 500000000000 : ℚ) := by norm_num only
    have hc : (((584998297 / 500000000000 : ℚ) +
        (9341738503 / 1000000000000000000 : ℚ) / (2194442299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1399856449 / 1000000000000 : ℚ) + (829446311 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3983895899 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12747]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12747 :
    2 * 160 < 12747 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999771 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12747 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12748 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12748. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12748 : WorldParameters where
  hiddenCharge := (1169953531 / 1000000000000 : ℝ)
  frame := (31248238951 / 50000000000 : ℝ)
  moment := (9339823733 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12748 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (184277518319 / 125000000000 : ℝ)
    root := (8462986759 / 1000000000000 : ℝ) }

noncomputable def scalar12748 : ScalarCertificate 12748 world12748 agent12748 where
  dimensionLo := 12748
  dimensionHi := 12748
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2194800399 / 1000000000000 : ℝ)
  frameLo := (31248238951 / 50000000000 : ℝ)
  frameHi := (184277518319 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12748]
  agentFrame_pos := by norm_num only [agent12748]
  worldRadius := (2194800399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12748]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1398677597 / 1000000000000 : ℝ)
  lowerTail := (1657595339 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (398212107 / 50000000000 : ℝ)
  ledger := by
    have h : (1169953531 / 1000000000000 : ℚ) +
        (9339823733 / 1000000000000000000 : ℚ) / (2194800399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1398677597 / 1000000000000 : ℚ) + (1657595339 / 1000000000000 : ℚ) ≤
        (398212107 / 50000000000 : ℚ) := by norm_num only
    have hc : (((1169953531 / 1000000000000 : ℚ) +
        (9339823733 / 1000000000000000000 : ℚ) / (2194800399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1398677597 / 1000000000000 : ℚ) + (1657595339 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((398212107 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12748]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12748 :
    2 * 160 < 12748 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999163 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12748 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12749 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12749. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12749 : WorldParameters where
  hiddenCharge := (1169910479 / 1000000000000 : ℝ)
  frame := (156237760699 / 250000000000 : ℝ)
  moment := (9337909511 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12749 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (184273556171 / 125000000000 : ℝ)
    root := (423115717 / 50000000000 : ℝ) }

noncomputable def scalar12749 : ScalarCertificate 12749 world12749 agent12749 where
  dimensionLo := 12749
  dimensionHi := 12749
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2195158399 / 1000000000000 : ℝ)
  frameLo := (156237760699 / 250000000000 : ℝ)
  frameHi := (184273556171 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12749]
  agentFrame_pos := by norm_num only [agent12749]
  worldRadius := (2195158399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12749]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (279499949 / 200000000000 : ℝ)
  lowerTail := (828149543 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3980347691 / 500000000000 : ℝ)
  ledger := by
    have h : (1169910479 / 1000000000000 : ℚ) +
        (9337909511 / 1000000000000000000 : ℚ) / (2195158399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (279499949 / 200000000000 : ℚ) + (828149543 / 500000000000 : ℚ) ≤
        (3980347691 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1169910479 / 1000000000000 : ℚ) +
        (9337909511 / 1000000000000000000 : ℚ) / (2195158399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (279499949 / 200000000000 : ℚ) + (828149543 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3980347691 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12749]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12749 :
    2 * 160 < 12749 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995633 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12749 {← IO.monoMsNow}" : IO Unit)
