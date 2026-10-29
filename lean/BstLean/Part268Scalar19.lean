import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12825 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12825. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12825 : WorldParameters where
  hiddenCharge := (29166787 / 25000000000 : ℝ)
  frame := (124782693487 / 200000000000 : ℝ)
  moment := (9194018017 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12825 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367793492221 / 250000000000 : ℝ)
    root := (8411805373 / 1000000000000 : ℝ) }

noncomputable def scalar12825 : ScalarCertificate 12825 world12825 agent12825 where
  dimensionLo := 12825
  dimensionHi := 12825
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2223317299 / 1000000000000 : ℝ)
  frameLo := (124782693487 / 200000000000 : ℝ)
  frameHi := (367793492221 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12825]
  agentFrame_pos := by norm_num only [agent12825]
  worldRadius := (2223317299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12825]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1309352313 / 1000000000000 : ℝ)
  lowerTail := (1558710191 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7693835061 / 1000000000000 : ℝ)
  ledger := by
    have h : (29166787 / 25000000000 : ℚ) +
        (9194018017 / 1000000000000000000 : ℚ) / (2223317299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1309352313 / 1000000000000 : ℚ) + (1558710191 / 1000000000000 : ℚ) ≤
        (7693835061 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((29166787 / 25000000000 : ℚ) +
        (9194018017 / 1000000000000000000 : ℚ) / (2223317299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1309352313 / 1000000000000 : ℚ) + (1558710191 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7693835061 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12825]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12825 :
    2 * 160 < 12825 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994717 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12825 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12826 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12826. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12826 : WorldParameters where
  hiddenCharge := (1166629291 / 1000000000000 : ℝ)
  frame := (623899898493 / 1000000000000 : ℝ)
  moment := (4596072711 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12826 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471143241697 / 1000000000000 : ℝ)
    root := (8411148427 / 1000000000000 : ℝ) }

noncomputable def scalar12826 : ScalarCertificate 12826 world12826 agent12826 where
  dimensionLo := 12826
  dimensionHi := 12826
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2223676299 / 1000000000000 : ℝ)
  frameLo := (623899898493 / 1000000000000 : ℝ)
  frameHi := (1471143241697 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12826]
  agentFrame_pos := by norm_num only [agent12826]
  worldRadius := (2223676299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12826]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1308260213 / 1000000000000 : ℝ)
  lowerTail := (1557503093 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7690514459 / 1000000000000 : ℝ)
  ledger := by
    have h : (1166629291 / 1000000000000 : ℚ) +
        (4596072711 / 500000000000000000 : ℚ) / (2223676299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1308260213 / 1000000000000 : ℚ) + (1557503093 / 1000000000000 : ℚ) ≤
        (7690514459 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1166629291 / 1000000000000 : ℚ) +
        (4596072711 / 500000000000000000 : ℚ) / (2223676299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1308260213 / 1000000000000 : ℚ) + (1557503093 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7690514459 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12826]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12826 :
    2 * 160 < 12826 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (171874971 / 15625000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12826 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12827 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12827. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12827 : WorldParameters where
  hiddenCharge := (1166587113 / 1000000000000 : ℝ)
  frame := (623886331701 / 1000000000000 : ℝ)
  moment := (114878417 / 12500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12827 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471112533571 / 1000000000000 : ℝ)
    root := (8410491677 / 1000000000000 : ℝ) }

noncomputable def scalar12827 : ScalarCertificate 12827 world12827 agent12827 where
  dimensionLo := 12827
  dimensionHi := 12827
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2224035499 / 1000000000000 : ℝ)
  frameLo := (623886331701 / 1000000000000 : ℝ)
  frameHi := (1471112533571 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12827]
  agentFrame_pos := by norm_num only [agent12827]
  worldRadius := (2224035499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12827]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (653584669 / 500000000000 : ℝ)
  lowerTail := (389074321 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1921799173 / 250000000000 : ℝ)
  ledger := by
    have h : (1166587113 / 1000000000000 : ℚ) +
        (114878417 / 12500000000000000 : ℚ) / (2224035499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (653584669 / 500000000000 : ℚ) + (389074321 / 250000000000 : ℚ) ≤
        (1921799173 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1166587113 / 1000000000000 : ℚ) +
        (114878417 / 12500000000000000 : ℚ) / (2224035499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (653584669 / 500000000000 : ℚ) + (389074321 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1921799173 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12827]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12827 :
    2 * 160 < 12827 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999187 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12827 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12828 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12828. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12828 : WorldParameters where
  hiddenCharge := (583272473 / 500000000000 : ℝ)
  frame := (31193638353 / 50000000000 : ℝ)
  moment := (918840183 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12828 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735540922249 / 500000000000 : ℝ)
    root := (4204917561 / 500000000000 : ℝ) }

noncomputable def scalar12828 : ScalarCertificate 12828 world12828 agent12828 where
  dimensionLo := 12828
  dimensionHi := 12828
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2224394599 / 1000000000000 : ℝ)
  frameLo := (31193638353 / 50000000000 : ℝ)
  frameHi := (735540922249 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12828]
  agentFrame_pos := by norm_num only [agent12828]
  worldRadius := (2224394599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12828]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1306079449 / 1000000000000 : ℝ)
  lowerTail := (622037 / 400000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1536776351 / 200000000000 : ℝ)
  ledger := by
    have h : (583272473 / 500000000000 : ℚ) +
        (918840183 / 100000000000000000 : ℚ) / (2224394599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1306079449 / 1000000000000 : ℚ) + (622037 / 400000000 : ℚ) ≤
        (1536776351 / 200000000000 : ℚ) := by norm_num only
    have hc : (((583272473 / 500000000000 : ℚ) +
        (918840183 / 100000000000000000 : ℚ) / (2224394599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1306079449 / 1000000000000 : ℚ) + (622037 / 400000000 : ℚ) : ℚ) : ℝ) ≤
        ((1536776351 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12828]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12828 :
    2 * 160 < 12828 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995381 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12828 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12829 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12829. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12829 : WorldParameters where
  hiddenCharge := (1166502791 / 1000000000000 : ℝ)
  frame := (62385920457 / 100000000000 : ℝ)
  moment := (9186530833 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12829 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471051168583 / 1000000000000 : ℝ)
    root := (8409178829 / 1000000000000 : ℝ) }

noncomputable def scalar12829 : ScalarCertificate 12829 world12829 agent12829 where
  dimensionLo := 12829
  dimensionHi := 12829
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2224753699 / 1000000000000 : ℝ)
  frameLo := (62385920457 / 100000000000 : ℝ)
  frameHi := (1471051168583 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12829]
  agentFrame_pos := by norm_num only [agent12829]
  worldRadius := (2224753699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12829]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1304990651 / 1000000000000 : ℝ)
  lowerTail := (97118053 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (240017803 / 31250000000 : ℝ)
  ledger := by
    have h : (1166502791 / 1000000000000 : ℚ) +
        (9186530833 / 1000000000000000000 : ℚ) / (2224753699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1304990651 / 1000000000000 : ℚ) + (97118053 / 62500000000 : ℚ) ≤
        (240017803 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1166502791 / 1000000000000 : ℚ) +
        (9186530833 / 1000000000000000000 : ℚ) / (2224753699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1304990651 / 1000000000000 : ℚ) + (97118053 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((240017803 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12829]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12829 :
    2 * 160 < 12829 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995359 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12829 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12830 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12830. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12830 : WorldParameters where
  hiddenCharge := (583230323 / 500000000000 : ℝ)
  frame := (155961411057 / 250000000000 : ℝ)
  moment := (9184660369 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12830 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470940674243 / 1000000000000 : ℝ)
    root := (1681704533 / 200000000000 : ℝ) }

noncomputable def scalar12830 : ScalarCertificate 12830 world12830 agent12830 where
  dimensionLo := 12830
  dimensionHi := 12830
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2225226699 / 1000000000000 : ℝ)
  frameLo := (155961411057 / 250000000000 : ℝ)
  frameHi := (1470940674243 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12830]
  agentFrame_pos := by norm_num only [agent12830]
  worldRadius := (2225226699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12830]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1303669481 / 1000000000000 : ℝ)
  lowerTail := (1552383301 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7676534121 / 1000000000000 : ℝ)
  ledger := by
    have h : (583230323 / 500000000000 : ℚ) +
        (9184660369 / 1000000000000000000 : ℚ) / (2225226699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1303669481 / 1000000000000 : ℚ) + (1552383301 / 1000000000000 : ℚ) ≤
        (7676534121 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((583230323 / 500000000000 : ℚ) +
        (9184660369 / 1000000000000000000 : ℚ) / (2225226699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1303669481 / 1000000000000 : ℚ) + (1552383301 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7676534121 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12830]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12830 :
    2 * 160 < 12830 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998287 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12830 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12831 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12831. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12831 : WorldParameters where
  hiddenCharge := (72901157 / 62500000000 : ℝ)
  frame := (155958021509 / 250000000000 : ℝ)
  moment := (9182790437 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12831 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735454859113 / 500000000000 : ℝ)
    root := (8407866697 / 1000000000000 : ℝ) }

noncomputable def scalar12831 : ScalarCertificate 12831 world12831 agent12831 where
  dimensionLo := 12831
  dimensionHi := 12831
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2225586399 / 1000000000000 : ℝ)
  frameLo := (155958021509 / 250000000000 : ℝ)
  frameHi := (735454859113 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12831]
  agentFrame_pos := by norm_num only [agent12831]
  worldRadius := (2225586399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12831]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (13025821 / 10000000000 : ℝ)
  lowerTail := (775590463 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (767322519 / 100000000000 : ℝ)
  ledger := by
    have h : (72901157 / 62500000000 : ℚ) +
        (9182790437 / 1000000000000000000 : ℚ) / (2225586399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (13025821 / 10000000000 : ℚ) + (775590463 / 500000000000 : ℚ) ≤
        (767322519 / 100000000000 : ℚ) := by norm_num only
    have hc : (((72901157 / 62500000000 : ℚ) +
        (9182790437 / 1000000000000000000 : ℚ) / (2225586399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (13025821 / 10000000000 : ℚ) + (775590463 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((767322519 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12831]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12831 :
    2 * 160 < 12831 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996807 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12831 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12832 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12832. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12832 : WorldParameters where
  hiddenCharge := (1166376389 / 1000000000000 : ℝ)
  frame := (77977316249 / 125000000000 : ℝ)
  moment := (2295230259 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12832 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (29417574757 / 20000000000 : ℝ)
    root := (336288437 / 40000000000 : ℝ) }

noncomputable def scalar12832 : ScalarCertificate 12832 world12832 agent12832 where
  dimensionLo := 12832
  dimensionHi := 12832
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2225945999 / 1000000000000 : ℝ)
  frameLo := (77977316249 / 125000000000 : ℝ)
  frameHi := (29417574757 / 20000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12832]
  agentFrame_pos := by norm_num only [agent12832]
  worldRadius := (2225945999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12832]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (52059821 / 40000000000 : ℝ)
  lowerTail := (1549979353 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7669918689 / 1000000000000 : ℝ)
  ledger := by
    have h : (1166376389 / 1000000000000 : ℚ) +
        (2295230259 / 250000000000000000 : ℚ) / (2225945999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (52059821 / 40000000000 : ℚ) + (1549979353 / 1000000000000 : ℚ) ≤
        (7669918689 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1166376389 / 1000000000000 : ℚ) +
        (2295230259 / 250000000000000000 : ℚ) / (2225945999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (52059821 / 40000000000 : ℚ) + (1549979353 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7669918689 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12832]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12832 :
    2 * 160 < 12832 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999317 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12832 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12833 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12833. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12833 : WorldParameters where
  hiddenCharge := (1166334277 / 1000000000000 : ℝ)
  frame := (19493905503 / 31250000000 : ℝ)
  moment := (1147381521 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12833 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (91927986033 / 62500000000 : ℝ)
    root := (8406555347 / 1000000000000 : ℝ) }

noncomputable def scalar12833 : ScalarCertificate 12833 world12833 agent12833 where
  dimensionLo := 12833
  dimensionHi := 12833
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2226305599 / 1000000000000 : ℝ)
  frameLo := (19493905503 / 31250000000 : ℝ)
  frameHi := (91927986033 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12833]
  agentFrame_pos := by norm_num only [agent12833]
  worldRadius := (2226305599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12833]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1300410011 / 1000000000000 : ℝ)
  lowerTail := (1548778889 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (239581719 / 31250000000 : ℝ)
  ledger := by
    have h : (1166334277 / 1000000000000 : ℚ) +
        (1147381521 / 125000000000000000 : ℚ) / (2226305599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1300410011 / 1000000000000 : ℚ) + (1548778889 / 1000000000000 : ℚ) ≤
        (239581719 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1166334277 / 1000000000000 : ℚ) +
        (1147381521 / 125000000000000000 : ℚ) / (2226305599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1300410011 / 1000000000000 : ℚ) + (1548778889 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((239581719 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12833]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12833 :
    2 * 160 < 12833 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999131 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12833 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12834 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12834. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12834 : WorldParameters where
  hiddenCharge := (1166292177 / 1000000000000 : ℝ)
  frame := (623791424347 / 1000000000000 : ℝ)
  moment := (917718383 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12834 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470816834251 / 1000000000000 : ℝ)
    root := (1681179993 / 200000000000 : ℝ) }

noncomputable def scalar12834 : ScalarCertificate 12834 world12834 agent12834 where
  dimensionLo := 12834
  dimensionHi := 12834
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2226665199 / 1000000000000 : ℝ)
  frameLo := (623791424347 / 1000000000000 : ℝ)
  frameHi := (1470816834251 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12834]
  agentFrame_pos := by norm_num only [agent12834]
  worldRadius := (2226665199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12834]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (324831389 / 250000000000 : ℝ)
  lowerTail := (386894883 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3831657073 / 500000000000 : ℝ)
  ledger := by
    have h : (1166292177 / 1000000000000 : ℚ) +
        (917718383 / 100000000000000000 : ℚ) / (2226665199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (324831389 / 250000000000 : ℚ) + (386894883 / 250000000000 : ℚ) ≤
        (3831657073 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1166292177 / 1000000000000 : ℚ) +
        (917718383 / 100000000000000000 : ℚ) / (2226665199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (324831389 / 250000000000 : ℚ) + (386894883 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3831657073 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12834]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12834 :
    2 * 160 < 12834 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995667 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12834 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12835 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12835. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12835 : WorldParameters where
  hiddenCharge := (1166250087 / 1000000000000 : ℝ)
  frame := (77972234343 / 125000000000 : ℝ)
  moment := (367012641 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12835 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367696476279 / 250000000000 : ℝ)
    root := (8405244777 / 1000000000000 : ℝ) }

noncomputable def scalar12835 : ScalarCertificate 12835 world12835 agent12835 where
  dimensionLo := 12835
  dimensionHi := 12835
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2227024899 / 1000000000000 : ℝ)
  frameLo := (77972234343 / 125000000000 : ℝ)
  frameHi := (367696476279 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12835]
  agentFrame_pos := by norm_num only [agent12835]
  worldRadius := (2227024899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12835]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (649121107 / 500000000000 : ℝ)
  lowerTail := (773190669 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3830008023 / 500000000000 : ℝ)
  ledger := by
    have h : (1166250087 / 1000000000000 : ℚ) +
        (367012641 / 40000000000000000 : ℚ) / (2227024899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (649121107 / 500000000000 : ℚ) + (773190669 / 500000000000 : ℚ) ≤
        (3830008023 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1166250087 / 1000000000000 : ℚ) +
        (367012641 / 40000000000000000 : ℚ) / (2227024899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (649121107 / 500000000000 : ℚ) + (773190669 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3830008023 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12835]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12835 :
    2 * 160 < 12835 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998203 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12835 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12836 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12836. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12836 : WorldParameters where
  hiddenCharge := (1166208009 / 1000000000000 : ℝ)
  frame := (77970540911 / 125000000000 : ℝ)
  moment := (7338759 / 800000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12836 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147075499501 / 100000000000 : ℝ)
    root := (1050573723 / 125000000000 : ℝ) }

noncomputable def scalar12836 : ScalarCertificate 12836 world12836 agent12836 where
  dimensionLo := 12836
  dimensionHi := 12836
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2227384599 / 1000000000000 : ℝ)
  frameLo := (77970540911 / 125000000000 : ℝ)
  frameHi := (147075499501 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12836]
  agentFrame_pos := by norm_num only [agent12836]
  worldRadius := (2227384599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12836]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (129715993 / 100000000000 : ℝ)
  lowerTail := (1545184249 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3828360379 / 500000000000 : ℝ)
  ledger := by
    have h : (1166208009 / 1000000000000 : ℚ) +
        (7338759 / 800000000000000 : ℚ) / (2227384599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (129715993 / 100000000000 : ℚ) + (1545184249 / 1000000000000 : ℚ) ≤
        (3828360379 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1166208009 / 1000000000000 : ℚ) +
        (7338759 / 800000000000000 : ℚ) / (2227384599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (129715993 / 100000000000 : ℚ) + (1545184249 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3828360379 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12836]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12836 :
    2 * 160 < 12836 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (79999959 / 8000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12836 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12837 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12837. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12837 : WorldParameters where
  hiddenCharge := (1166165941 / 1000000000000 : ℝ)
  frame := (311875390989 / 500000000000 : ℝ)
  moment := (9171582007 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12837 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470724098031 / 1000000000000 : ℝ)
    root := (4201967493 / 500000000000 : ℝ) }

noncomputable def scalar12837 : ScalarCertificate 12837 world12837 agent12837 where
  dimensionLo := 12837
  dimensionHi := 12837
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2227744199 / 1000000000000 : ℝ)
  frameLo := (311875390989 / 500000000000 : ℝ)
  frameHi := (1470724098031 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12837]
  agentFrame_pos := by norm_num only [agent12837]
  worldRadius := (2227744199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12837]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1296078599 / 1000000000000 : ℝ)
  lowerTail := (771994073 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3826714113 / 500000000000 : ℝ)
  ledger := by
    have h : (1166165941 / 1000000000000 : ℚ) +
        (9171582007 / 1000000000000000000 : ℚ) / (2227744199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1296078599 / 1000000000000 : ℚ) + (771994073 / 500000000000 : ℚ) ≤
        (3826714113 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1166165941 / 1000000000000 : ℚ) +
        (9171582007 / 1000000000000000000 : ℚ) / (2227744199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1296078599 / 1000000000000 : ℚ) + (771994073 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3826714113 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12837]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12837 :
    2 * 160 < 12837 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996637 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12837 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12838 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12838. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12838 : WorldParameters where
  hiddenCharge := (291530971 / 250000000000 : ℝ)
  frame := (623737238813 / 1000000000000 : ℝ)
  moment := (4584857897 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12838 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (45959163127 / 31250000000 : ℝ)
    root := (4201640191 / 500000000000 : ℝ) }

noncomputable def scalar12838 : ScalarCertificate 12838 world12838 agent12838 where
  dimensionLo := 12838
  dimensionHi := 12838
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2228103899 / 1000000000000 : ℝ)
  frameLo := (623737238813 / 1000000000000 : ℝ)
  frameHi := (45959163127 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12838]
  agentFrame_pos := by norm_num only [agent12838]
  worldRadius := (2228103899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12838]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1294998401 / 1000000000000 : ℝ)
  lowerTail := (96424577 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3825069251 / 500000000000 : ℝ)
  ledger := by
    have h : (291530971 / 250000000000 : ℚ) +
        (4584857897 / 500000000000000000 : ℚ) / (2228103899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1294998401 / 1000000000000 : ℚ) + (96424577 / 62500000000 : ℚ) ≤
        (3825069251 / 500000000000 : ℚ) := by norm_num only
    have hc : (((291530971 / 250000000000 : ℚ) +
        (4584857897 / 500000000000000000 : ℚ) / (2228103899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1294998401 / 1000000000000 : ℚ) + (96424577 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((3825069251 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12838]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12838 :
    2 * 160 < 12838 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999217 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12838 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12839 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12839. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12839 : WorldParameters where
  hiddenCharge := (1166081839 / 1000000000000 : ℝ)
  frame := (4872841389 / 7812500000 : ℝ)
  moment := (71623829 / 7812500000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12839 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470662355207 / 1000000000000 : ℝ)
    root := (8402625973 / 1000000000000 : ℝ) }

noncomputable def scalar12839 : ScalarCertificate 12839 world12839 agent12839 where
  dimensionLo := 12839
  dimensionHi := 12839
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2228463499 / 1000000000000 : ℝ)
  frameLo := (4872841389 / 7812500000 : ℝ)
  frameHi := (1470662355207 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12839]
  agentFrame_pos := by norm_num only [agent12839]
  worldRadius := (2228463499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12839]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (646959577 / 500000000000 : ℝ)
  lowerTail := (1541599303 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7646851527 / 1000000000000 : ℝ)
  ledger := by
    have h : (1166081839 / 1000000000000 : ℚ) +
        (71623829 / 7812500000000000 : ℚ) / (2228463499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (646959577 / 500000000000 : ℚ) + (1541599303 / 1000000000000 : ℚ) ≤
        (7646851527 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1166081839 / 1000000000000 : ℚ) +
        (71623829 / 7812500000000000 : ℚ) / (2228463499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (646959577 / 500000000000 : ℚ) + (1541599303 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7646851527 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12839]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12839 :
    2 * 160 < 12839 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (156249981 / 15625000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12839 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12840 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12840. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12840 : WorldParameters where
  hiddenCharge := (291509951 / 250000000000 : ℝ)
  frame := (124742031783 / 200000000000 : ℝ)
  moment := (28643703 / 3125000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12840 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735275868639 / 500000000000 : ℝ)
    root := (4200985879 / 500000000000 : ℝ) }

noncomputable def scalar12840 : ScalarCertificate 12840 world12840 agent12840 where
  dimensionLo := 12840
  dimensionHi := 12840
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2228937499 / 1000000000000 : ℝ)
  frameLo := (124742031783 / 200000000000 : ℝ)
  frameHi := (735275868639 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12840]
  agentFrame_pos := by norm_num only [agent12840]
  worldRadius := (2228937499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12840]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (51704393 / 40000000000 : ℝ)
  lowerTail := (770053099 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1528569309 / 200000000000 : ℝ)
  ledger := by
    have h : (291509951 / 250000000000 : ℚ) +
        (28643703 / 3125000000000000 : ℚ) / (2228937499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (51704393 / 40000000000 : ℚ) + (770053099 / 500000000000 : ℚ) ≤
        (1528569309 / 200000000000 : ℚ) := by norm_num only
    have hc : (((291509951 / 250000000000 : ℚ) +
        (28643703 / 3125000000000000 : ℚ) / (2228937499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (51704393 / 40000000000 : ℚ) + (770053099 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1528569309 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12840]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12840 :
    2 * 160 < 12840 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999123 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12840 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12841 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12841. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12841 : WorldParameters where
  hiddenCharge := (58299889 / 50000000000 : ℝ)
  frame := (311848311091 / 500000000000 : ℝ)
  moment := (4582060169 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12841 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470520911327 / 1000000000000 : ℝ)
    root := (8401317737 / 1000000000000 : ℝ) }

noncomputable def scalar12841 : ScalarCertificate 12841 world12841 agent12841 where
  dimensionLo := 12841
  dimensionHi := 12841
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2229297199 / 1000000000000 : ℝ)
  frameLo := (311848311091 / 500000000000 : ℝ)
  frameHi := (1470520911327 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12841]
  agentFrame_pos := by norm_num only [agent12841]
  worldRadius := (2229297199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12841]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (32288323 / 25000000000 : ℝ)
  lowerTail := (769457373 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7639565651 / 1000000000000 : ℝ)
  ledger := by
    have h : (58299889 / 50000000000 : ℚ) +
        (4582060169 / 500000000000000000 : ℚ) / (2229297199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (32288323 / 25000000000 : ℚ) + (769457373 / 500000000000 : ℚ) ≤
        (7639565651 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((58299889 / 50000000000 : ℚ) +
        (4582060169 / 500000000000000000 : ℚ) / (2229297199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (32288323 / 25000000000 : ℚ) + (769457373 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7639565651 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12841]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12841 :
    2 * 160 < 12841 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997079 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12841 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12842 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12842. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12842 : WorldParameters where
  hiddenCharge := (145744471 / 125000000000 : ℝ)
  frame := (623683087591 / 1000000000000 : ℝ)
  moment := (9162256247 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12842 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470490098463 / 1000000000000 : ℝ)
    root := (8400663911 / 1000000000000 : ℝ) }

noncomputable def scalar12842 : ScalarCertificate 12842 world12842 agent12842 where
  dimensionLo := 12842
  dimensionHi := 12842
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2229656999 / 1000000000000 : ℝ)
  frameLo := (623683087591 / 1000000000000 : ℝ)
  frameHi := (1470490098463 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12842]
  agentFrame_pos := by norm_num only [agent12842]
  worldRadius := (2229656999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12842]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1290457119 / 1000000000000 : ℝ)
  lowerTail := (48053889 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3818143749 / 500000000000 : ℝ)
  ledger := by
    have h : (145744471 / 125000000000 : ℚ) +
        (9162256247 / 1000000000000000000 : ℚ) / (2229656999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1290457119 / 1000000000000 : ℚ) + (48053889 / 31250000000 : ℚ) ≤
        (3818143749 / 500000000000 : ℚ) := by norm_num only
    have hc : (((145744471 / 125000000000 : ℚ) +
        (9162256247 / 1000000000000000000 : ℚ) / (2229656999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1290457119 / 1000000000000 : ℚ) + (48053889 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((3818143749 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12842]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12842 :
    2 * 160 < 12842 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999111 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12842 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12843 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12843. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12843 : WorldParameters where
  hiddenCharge := (582956883 / 500000000000 : ℝ)
  frame := (77958694393 / 125000000000 : ℝ)
  moment := (1832078537 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12843 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470459304567 / 1000000000000 : ℝ)
    root := (4200005139 / 500000000000 : ℝ) }

noncomputable def scalar12843 : ScalarCertificate 12843 world12843 agent12843 where
  dimensionLo := 12843
  dimensionHi := 12843
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2230016699 / 1000000000000 : ℝ)
  frameLo := (77958694393 / 125000000000 : ℝ)
  frameHi := (1470459304567 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12843]
  agentFrame_pos := by norm_num only [agent12843]
  worldRadius := (2230016699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12843]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1289382289 / 1000000000000 : ℝ)
  lowerTail := (38413379 / 25000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3816506069 / 500000000000 : ℝ)
  ledger := by
    have h : (582956883 / 500000000000 : ℚ) +
        (1832078537 / 200000000000000000 : ℚ) / (2230016699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1289382289 / 1000000000000 : ℚ) + (38413379 / 25000000000 : ℚ) ≤
        (3816506069 / 500000000000 : ℚ) := by norm_num only
    have hc : (((582956883 / 500000000000 : ℚ) +
        (1832078537 / 200000000000000000 : ℚ) / (2230016699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1289382289 / 1000000000000 : ℚ) + (38413379 / 25000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3816506069 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12843]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12843 :
    2 * 160 < 12843 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996937 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12843 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12844 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12844. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12844 : WorldParameters where
  hiddenCharge := (36433493 / 31250000000 : ℝ)
  frame := (623656024837 / 1000000000000 : ℝ)
  moment := (9158529653 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12844 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735214261871 / 500000000000 : ℝ)
    root := (8399356839 / 1000000000000 : ℝ) }

noncomputable def scalar12844 : ScalarCertificate 12844 world12844 agent12844 where
  dimensionLo := 12844
  dimensionHi := 12844
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2230376299 / 1000000000000 : ℝ)
  frameLo := (623656024837 / 1000000000000 : ℝ)
  frameHi := (735214261871 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12844]
  agentFrame_pos := by norm_num only [agent12844]
  worldRadius := (2230376299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12844]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (322077101 / 250000000000 : ℝ)
  lowerTail := (1535346851 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7629739513 / 1000000000000 : ℝ)
  ledger := by
    have h : (36433493 / 31250000000 : ℚ) +
        (9158529653 / 1000000000000000000 : ℚ) / (2230376299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (322077101 / 250000000000 : ℚ) + (1535346851 / 1000000000000 : ℚ) ≤
        (7629739513 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((36433493 / 31250000000 : ℚ) +
        (9158529653 / 1000000000000000000 : ℚ) / (2230376299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (322077101 / 250000000000 : ℚ) + (1535346851 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7629739513 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12844]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12844 :
    2 * 160 < 12844 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999399 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12844 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12845 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12845. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12845 : WorldParameters where
  hiddenCharge := (291457449 / 250000000000 : ℝ)
  frame := (623642496673 / 1000000000000 : ℝ)
  moment := (183133343 / 20000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12845 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470397761869 / 1000000000000 : ℝ)
    root := (8398703593 / 1000000000000 : ℝ) }

noncomputable def scalar12845 : ScalarCertificate 12845 world12845 agent12845 where
  dimensionLo := 12845
  dimensionHi := 12845
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2230736099 / 1000000000000 : ℝ)
  frameLo := (623642496673 / 1000000000000 : ℝ)
  frameHi := (1470397761869 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12845]
  agentFrame_pos := by norm_num only [agent12845]
  worldRadius := (2230736099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12845]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (643617861 / 500000000000 : ℝ)
  lowerTail := (23971247 / 15625000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (305058787 / 40000000000 : ℝ)
  ledger := by
    have h : (291457449 / 250000000000 : ℚ) +
        (183133343 / 20000000000000000 : ℚ) / (2230736099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (643617861 / 500000000000 : ℚ) + (23971247 / 15625000000 : ℚ) ≤
        (305058787 / 40000000000 : ℚ) := by norm_num only
    have hc : (((291457449 / 250000000000 : ℚ) +
        (183133343 / 20000000000000000 : ℚ) / (2230736099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (643617861 / 500000000000 : ℚ) + (23971247 / 15625000000 : ℚ) : ℚ) : ℝ) ≤
        ((305058787 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12845]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12845 :
    2 * 160 < 12845 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999093 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12845 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12846 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12846. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12846 : WorldParameters where
  hiddenCharge := (1165787827 / 1000000000000 : ℝ)
  frame := (623628970649 / 1000000000000 : ℝ)
  moment := (9154805177 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12846 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470367018941 / 1000000000000 : ℝ)
    root := (8398050541 / 1000000000000 : ℝ) }

noncomputable def scalar12846 : ScalarCertificate 12846 world12846 agent12846 where
  dimensionLo := 12846
  dimensionHi := 12846
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2231095699 / 1000000000000 : ℝ)
  frameLo := (623628970649 / 1000000000000 : ℝ)
  frameHi := (1470367018941 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12846]
  agentFrame_pos := by norm_num only [agent12846]
  worldRadius := (2231095699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12846]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1286163929 / 1000000000000 : ℝ)
  lowerTail := (766486843 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7623202621 / 1000000000000 : ℝ)
  ledger := by
    have h : (1165787827 / 1000000000000 : ℚ) +
        (9154805177 / 1000000000000000000 : ℚ) / (2231095699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1286163929 / 1000000000000 : ℚ) + (766486843 / 500000000000 : ℚ) ≤
        (7623202621 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1165787827 / 1000000000000 : ℚ) +
        (9154805177 / 1000000000000000000 : ℚ) / (2231095699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1286163929 / 1000000000000 : ℚ) + (766486843 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7623202621 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12846]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12846 :
    2 * 160 < 12846 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999997539 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12846 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12847 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12847. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12847 : WorldParameters where
  hiddenCharge := (116574587 / 100000000000 : ℝ)
  frame := (124723089353 / 200000000000 : ℝ)
  moment := (2288235933 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12847 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735168144529 / 500000000000 : ℝ)
    root := (8397397683 / 1000000000000 : ℝ) }

noncomputable def scalar12847 : ScalarCertificate 12847 world12847 agent12847 where
  dimensionLo := 12847
  dimensionHi := 12847
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2231455499 / 1000000000000 : ℝ)
  frameLo := (124723089353 / 200000000000 : ℝ)
  frameHi := (735168144529 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12847]
  agentFrame_pos := by norm_num only [agent12847]
  worldRadius := (2231455499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12847]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1285093313 / 1000000000000 : ℝ)
  lowerTail := (765894399 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1523987659 / 200000000000 : ℝ)
  ledger := by
    have h : (116574587 / 100000000000 : ℚ) +
        (2288235933 / 250000000000000000 : ℚ) / (2231455499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1285093313 / 1000000000000 : ℚ) + (765894399 / 500000000000 : ℚ) ≤
        (1523987659 / 200000000000 : ℚ) := by norm_num only
    have hc : (((116574587 / 100000000000 : ℚ) +
        (2288235933 / 250000000000000000 : ℚ) / (2231455499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1285093313 / 1000000000000 : ℚ) + (765894399 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1523987659 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12847]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12847 :
    2 * 160 < 12847 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499998763 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12847 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12848 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12848. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12848 : WorldParameters where
  hiddenCharge := (1165703923 / 1000000000000 : ℝ)
  frame := (623601925021 / 1000000000000 : ℝ)
  moment := (9151082817 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12848 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470305572213 / 1000000000000 : ℝ)
    root := (4198372509 / 500000000000 : ℝ) }

noncomputable def scalar12848 : ScalarCertificate 12848 world12848 agent12848 where
  dimensionLo := 12848
  dimensionHi := 12848
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2231815299 / 1000000000000 : ℝ)
  frameLo := (623601925021 / 1000000000000 : ℝ)
  frameHi := (1470305572213 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12848]
  agentFrame_pos := by norm_num only [agent12848]
  worldRadius := (2231815299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12848]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (256804743 / 200000000000 : ℝ)
  lowerTail := (382651243 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3808338347 / 500000000000 : ℝ)
  ledger := by
    have h : (1165703923 / 1000000000000 : ℚ) +
        (9151082817 / 1000000000000000000 : ℚ) / (2231815299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (256804743 / 200000000000 : ℚ) + (382651243 / 250000000000 : ℚ) ≤
        (3808338347 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1165703923 / 1000000000000 : ℚ) +
        (9151082817 / 1000000000000000000 : ℚ) / (2231815299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (256804743 / 200000000000 : ℚ) + (382651243 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3808338347 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12848]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12848 :
    2 * 160 < 12848 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998091 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12848 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12849 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12849. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12849 : WorldParameters where
  hiddenCharge := (1165661987 / 1000000000000 : ℝ)
  frame := (77948550677 / 125000000000 : ℝ)
  moment := (914922243 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12849 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470274874287 / 1000000000000 : ℝ)
    root := (4198046273 / 500000000000 : ℝ) }

noncomputable def scalar12849 : ScalarCertificate 12849 world12849 agent12849 where
  dimensionLo := 12849
  dimensionHi := 12849
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2232174999 / 1000000000000 : ℝ)
  frameLo := (77948550677 / 125000000000 : ℝ)
  frameHi := (1470274874287 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12849]
  agentFrame_pos := by norm_num only [agent12849]
  worldRadius := (2232174999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12849]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (641477541 / 500000000000 : ℝ)
  lowerTail := (382355537 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7613417867 / 1000000000000 : ℝ)
  ledger := by
    have h : (1165661987 / 1000000000000 : ℚ) +
        (914922243 / 100000000000000000 : ℚ) / (2232174999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (641477541 / 500000000000 : ℚ) + (382355537 / 250000000000 : ℚ) ≤
        (7613417867 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1165661987 / 1000000000000 : ℚ) +
        (914922243 / 100000000000000000 : ℚ) / (2232174999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (641477541 / 500000000000 : ℚ) + (382355537 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7613417867 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12849]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12849 :
    2 * 160 < 12849 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998569 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12849 {← IO.monoMsNow}" : IO Unit)
