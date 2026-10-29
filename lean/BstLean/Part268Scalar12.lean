import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12650 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12650. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12650 : WorldParameters where
  hiddenCharge := (234845659 / 200000000000 : ℝ)
  frame := (62632166113 / 100000000000 : ℝ)
  moment := (1906021919 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12650 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147810227913 / 100000000000 : ℝ)
    root := (1705979829 / 200000000000 : ℝ) }

noncomputable def scalar12650 : ScalarCertificate 12650 world12650 agent12650 where
  dimensionLo := 12650
  dimensionHi := 12650
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2158788399 / 1000000000000 : ℝ)
  frameLo := (62632166113 / 100000000000 : ℝ)
  frameHi := (147810227913 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12650]
  agentFrame_pos := by norm_num only [agent12650]
  worldRadius := (2158788399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12650]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (304449081 / 200000000000 : ℝ)
  lowerTail := (358726709 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8334179931 / 1000000000000 : ℝ)
  ledger := by
    have h : (234845659 / 200000000000 : ℚ) +
        (1906021919 / 200000000000000000 : ℚ) / (2158788399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (304449081 / 200000000000 : ℚ) + (358726709 / 200000000000 : ℚ) ≤
        (8334179931 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((234845659 / 200000000000 : ℚ) +
        (1906021919 / 200000000000000000 : ℚ) / (2158788399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (304449081 / 200000000000 : ℚ) + (358726709 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8334179931 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12650]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12650 :
    2 * 160 < 12650 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995979 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12650 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12651 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12651. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12651 : WorldParameters where
  hiddenCharge := (73386507 / 62500000000 : ℝ)
  frame := (313153853597 / 500000000000 : ℝ)
  moment := (9528140661 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12651 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1478069489271 / 1000000000000 : ℝ)
    root := (4264602963 / 500000000000 : ℝ) }

noncomputable def scalar12651 : ScalarCertificate 12651 world12651 agent12651 where
  dimensionLo := 12651
  dimensionHi := 12651
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2159144899 / 1000000000000 : ℝ)
  frameLo := (313153853597 / 500000000000 : ℝ)
  frameHi := (1478069489271 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12651]
  agentFrame_pos := by norm_num only [agent12651]
  worldRadius := (2159144899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12651]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (760474039 / 500000000000 : ℝ)
  lowerTail := (448053477 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8330321211 / 1000000000000 : ℝ)
  ledger := by
    have h : (73386507 / 62500000000 : ℚ) +
        (9528140661 / 1000000000000000000 : ℚ) / (2159144899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (760474039 / 500000000000 : ℚ) + (448053477 / 250000000000 : ℚ) ≤
        (8330321211 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((73386507 / 62500000000 : ℚ) +
        (9528140661 / 1000000000000000000 : ℚ) / (2159144899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (760474039 / 500000000000 : ℚ) + (448053477 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8330321211 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12651]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12651 :
    2 * 160 < 12651 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995551 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12651 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12652 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12652. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12652 : WorldParameters where
  hiddenCharge := (58706997 / 50000000000 : ℝ)
  frame := (626293755507 / 1000000000000 : ℝ)
  moment := (4763086147 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12652 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1478036714131 / 1000000000000 : ℝ)
    root := (4264256497 / 500000000000 : ℝ) }

noncomputable def scalar12652 : ScalarCertificate 12652 world12652 agent12652 where
  dimensionLo := 12652
  dimensionHi := 12652
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2159501499 / 1000000000000 : ℝ)
  frameLo := (626293755507 / 1000000000000 : ℝ)
  frameHi := (1478036714131 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12652]
  agentFrame_pos := by norm_num only [agent12652]
  worldRadius := (2159501499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12652]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (759826087 / 500000000000 : ℝ)
  lowerTail := (89539787 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8326465941 / 1000000000000 : ℝ)
  ledger := by
    have h : (58706997 / 50000000000 : ℚ) +
        (4763086147 / 500000000000000000 : ℚ) / (2159501499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (759826087 / 500000000000 : ℚ) + (89539787 / 50000000000 : ℚ) ≤
        (8326465941 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((58706997 / 50000000000 : ℚ) +
        (4763086147 / 500000000000000000 : ℚ) / (2159501499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (759826087 / 500000000000 : ℚ) + (89539787 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8326465941 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12652]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12652 :
    2 * 160 < 12652 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999891 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12652 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12653 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12653. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12653 : WorldParameters where
  hiddenCharge := (1174095781 / 1000000000000 : ℝ)
  frame := (626279806069 / 1000000000000 : ℝ)
  moment := (595262781 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12653 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1478003965553 / 1000000000000 : ℝ)
    root := (1705564043 / 200000000000 : ℝ) }

noncomputable def scalar12653 : ScalarCertificate 12653 world12653 agent12653 where
  dimensionLo := 12653
  dimensionHi := 12653
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2159858099 / 1000000000000 : ℝ)
  frameLo := (626279806069 / 1000000000000 : ℝ)
  frameHi := (1478003965553 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12653]
  agentFrame_pos := by norm_num only [agent12653]
  worldRadius := (2159858099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12653]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (759178767 / 500000000000 : ℝ)
  lowerTail := (894689443 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8322613997 / 1000000000000 : ℝ)
  ledger := by
    have h : (1174095781 / 1000000000000 : ℚ) +
        (595262781 / 62500000000000000 : ℚ) / (2159858099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (759178767 / 500000000000 : ℚ) + (894689443 / 500000000000 : ℚ) ≤
        (8322613997 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1174095781 / 1000000000000 : ℚ) +
        (595262781 / 62500000000000000 : ℚ) / (2159858099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (759178767 / 500000000000 : ℚ) + (894689443 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8322613997 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12653]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12653 :
    2 * 160 < 12653 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994473 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12653 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12654 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12654. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12654 : WorldParameters where
  hiddenCharge := (73378227 / 62500000000 : ℝ)
  frame := (1957080809 / 3125000000 : ℝ)
  moment := (1904447453 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12654 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (738985612873 / 500000000000 : ℝ)
    root := (1065890957 / 125000000000 : ℝ) }

noncomputable def scalar12654 : ScalarCertificate 12654 world12654 agent12654 where
  dimensionLo := 12654
  dimensionHi := 12654
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2160214699 / 1000000000000 : ℝ)
  frameLo := (1957080809 / 3125000000 : ℝ)
  frameHi := (738985612873 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12654]
  agentFrame_pos := by norm_num only [agent12654]
  worldRadius := (2160214699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12654]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (189633017 / 125000000000 : ℝ)
  lowerTail := (357592661 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8318765313 / 1000000000000 : ℝ)
  ledger := by
    have h : (73378227 / 62500000000 : ℚ) +
        (1904447453 / 200000000000000000 : ℚ) / (2160214699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (189633017 / 125000000000 : ℚ) + (357592661 / 200000000000 : ℚ) ≤
        (8318765313 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((73378227 / 62500000000 : ℚ) +
        (1904447453 / 200000000000000000 : ℚ) / (2160214699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (189633017 / 125000000000 : ℚ) + (357592661 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8318765313 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12654]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12654 :
    2 * 160 < 12654 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999881 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12654 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12655 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12655. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12655 : WorldParameters where
  hiddenCharge := (146750937 / 125000000000 : ℝ)
  frame := (313125956969 / 500000000000 : ℝ)
  moment := (9520270603 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12655 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (9237115703 / 6250000000 : ℝ)
    root := (2131608829 / 250000000000 : ℝ) }

noncomputable def scalar12655 : ScalarCertificate 12655 world12655 agent12655 where
  dimensionLo := 12655
  dimensionHi := 12655
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2160571199 / 1000000000000 : ℝ)
  frameLo := (313125956969 / 500000000000 : ℝ)
  frameHi := (9237115703 / 6250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12655]
  agentFrame_pos := by norm_num only [agent12655]
  worldRadius := (2160571199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12655]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (151577197 / 100000000000 : ℝ)
  lowerTail := (1786548997 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2078730017 / 250000000000 : ℝ)
  ledger := by
    have h : (146750937 / 125000000000 : ℚ) +
        (9520270603 / 1000000000000000000 : ℚ) / (2160571199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (151577197 / 100000000000 : ℚ) + (1786548997 / 1000000000000 : ℚ) ≤
        (2078730017 / 250000000000 : ℚ) := by norm_num only
    have hc : (((146750937 / 125000000000 : ℚ) +
        (9520270603 / 1000000000000000000 : ℚ) / (2160571199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (151577197 / 100000000000 : ℚ) + (1786548997 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2078730017 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12655]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12655 :
    2 * 160 < 12655 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997001 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12655 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12656 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12656. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12656 : WorldParameters where
  hiddenCharge := (293490843 / 250000000000 : ℝ)
  frame := (313118985621 / 500000000000 : ℝ)
  moment := (9518304507 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12656 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369476453473 / 250000000000 : ℝ)
    root := (4262871631 / 500000000000 : ℝ) }

noncomputable def scalar12656 : ScalarCertificate 12656 world12656 agent12656 where
  dimensionLo := 12656
  dimensionHi := 12656
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2160927699 / 1000000000000 : ℝ)
  frameLo := (313118985621 / 500000000000 : ℝ)
  frameHi := (369476453473 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12656]
  agentFrame_pos := by norm_num only [agent12656]
  worldRadius := (2160927699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12656]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (151448113 / 100000000000 : ℝ)
  lowerTail := (892568027 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4155539129 / 500000000000 : ℝ)
  ledger := by
    have h : (293490843 / 250000000000 : ℚ) +
        (9518304507 / 1000000000000000000 : ℚ) / (2160927699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (151448113 / 100000000000 : ℚ) + (892568027 / 500000000000 : ℚ) ≤
        (4155539129 / 500000000000 : ℚ) := by norm_num only
    have hc : (((293490843 / 250000000000 : ℚ) +
        (9518304507 / 1000000000000000000 : ℚ) / (2160927699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (151448113 / 100000000000 : ℚ) + (892568027 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4155539129 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12656]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12656 :
    2 * 160 < 12656 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998029 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12656 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12657 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12657. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12657 : WorldParameters where
  hiddenCharge := (1173919259 / 1000000000000 : ℝ)
  frame := (313112015397 / 500000000000 : ℝ)
  moment := (475816949 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12657 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1477873135897 / 1000000000000 : ℝ)
    root := (8525051361 / 1000000000000 : ℝ) }

noncomputable def scalar12657 : ScalarCertificate 12657 world12657 agent12657 where
  dimensionLo := 12657
  dimensionHi := 12657
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2161284399 / 1000000000000 : ℝ)
  frameLo := (313112015397 / 500000000000 : ℝ)
  frameHi := (1477873135897 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12657]
  agentFrame_pos := by norm_num only [agent12657]
  worldRadius := (2161284399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12657]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (756595851 / 500000000000 : ℝ)
  lowerTail := (891862291 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8307239699 / 1000000000000 : ℝ)
  ledger := by
    have h : (1173919259 / 1000000000000 : ℚ) +
        (475816949 / 50000000000000000 : ℚ) / (2161284399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (756595851 / 500000000000 : ℚ) + (891862291 / 500000000000 : ℚ) ≤
        (8307239699 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1173919259 / 1000000000000 : ℚ) +
        (475816949 / 50000000000000000 : ℚ) / (2161284399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (756595851 / 500000000000 : ℚ) + (891862291 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8307239699 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12657]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12657 :
    2 * 160 < 12657 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (439999873 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12657 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12658 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12658. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12658 : WorldParameters where
  hiddenCharge := (1173875157 / 1000000000000 : ℝ)
  frame := (626210092591 / 1000000000000 : ℝ)
  moment := (9514374019 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12658 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (18473005907 / 12500000000 : ℝ)
    root := (8524359679 / 1000000000000 : ℝ) }

noncomputable def scalar12658 : ScalarCertificate 12658 world12658 agent12658 where
  dimensionLo := 12658
  dimensionHi := 12658
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2161640899 / 1000000000000 : ℝ)
  frameLo := (626210092591 / 1000000000000 : ℝ)
  frameHi := (18473005907 / 12500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12658]
  agentFrame_pos := by norm_num only [agent12658]
  worldRadius := (2161640899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12658]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (377975839 / 250000000000 : ℝ)
  lowerTail := (356462843 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4151702223 / 500000000000 : ℝ)
  ledger := by
    have h : (1173875157 / 1000000000000 : ℚ) +
        (9514374019 / 1000000000000000000 : ℚ) / (2161640899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (377975839 / 250000000000 : ℚ) + (356462843 / 200000000000 : ℚ) ≤
        (4151702223 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1173875157 / 1000000000000 : ℚ) +
        (9514374019 / 1000000000000000000 : ℚ) / (2161640899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (377975839 / 250000000000 : ℚ) + (356462843 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4151702223 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12658]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12658 :
    2 * 160 < 12658 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999481 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12658 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12659 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12659. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12659 : WorldParameters where
  hiddenCharge := (293457767 / 250000000000 : ℝ)
  frame := (626196156633 / 1000000000000 : ℝ)
  moment := (76099277 / 8000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12659 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1477807829797 / 1000000000000 : ℝ)
    root := (1704733643 / 200000000000 : ℝ) }

noncomputable def scalar12659 : ScalarCertificate 12659 world12659 agent12659 where
  dimensionLo := 12659
  dimensionHi := 12659
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2161997499 / 1000000000000 : ℝ)
  frameLo := (626196156633 / 1000000000000 : ℝ)
  frameHi := (1477807829797 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12659]
  agentFrame_pos := by norm_num only [agent12659]
  worldRadius := (2161997499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12659]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (151061639 / 100000000000 : ℝ)
  lowerTail := (890452639 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4149786279 / 500000000000 : ℝ)
  ledger := by
    have h : (293457767 / 250000000000 : ℚ) +
        (76099277 / 8000000000000000 : ℚ) / (2161997499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (151061639 / 100000000000 : ℚ) + (890452639 / 500000000000 : ℚ) ≤
        (4149786279 / 500000000000 : ℚ) := by norm_num only
    have hc : (((293457767 / 250000000000 : ℚ) +
        (76099277 / 8000000000000000 : ℚ) / (2161997499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (151061639 / 100000000000 : ℚ) + (890452639 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4149786279 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12659]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12659 :
    2 * 160 < 12659 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999971 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12659 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12660 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12660. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12660 : WorldParameters where
  hiddenCharge := (117378699 / 100000000000 : ℝ)
  frame := (15654555573 / 25000000000 : ℝ)
  moment := (4755222899 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12660 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (295538679327 / 200000000000 : ℝ)
    root := (4261488519 / 500000000000 : ℝ) }

noncomputable def scalar12660 : ScalarCertificate 12660 world12660 agent12660 where
  dimensionLo := 12660
  dimensionHi := 12660
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2162465899 / 1000000000000 : ℝ)
  frameLo := (15654555573 / 25000000000 : ℝ)
  frameHi := (295538679327 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12660]
  agentFrame_pos := by norm_num only [agent12660]
  worldRadius := (2162465899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12660]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (377264367 / 250000000000 : ℝ)
  lowerTail := (1779146829 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2073727409 / 250000000000 : ℝ)
  ledger := by
    have h : (117378699 / 100000000000 : ℚ) +
        (4755222899 / 500000000000000000 : ℚ) / (2162465899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (377264367 / 250000000000 : ℚ) + (1779146829 / 1000000000000 : ℚ) ≤
        (2073727409 / 250000000000 : ℚ) := by norm_num only
    have hc : (((117378699 / 100000000000 : ℚ) +
        (4755222899 / 500000000000000000 : ℚ) / (2162465899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (377264367 / 250000000000 : ℚ) + (1779146829 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2073727409 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12660]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12660 :
    2 * 160 < 12660 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997921 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12660 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12661 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12661. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12661 : WorldParameters where
  hiddenCharge := (293435731 / 250000000000 : ℝ)
  frame := (626168291451 / 1000000000000 : ℝ)
  moment := (9508482537 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12661 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1477660790031 / 1000000000000 : ℝ)
    root := (2130571503 / 250000000000 : ℝ) }

noncomputable def scalar12661 : ScalarCertificate 12661 world12661 agent12661 where
  dimensionLo := 12661
  dimensionHi := 12661
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2162822499 / 1000000000000 : ℝ)
  frameLo := (626168291451 / 1000000000000 : ℝ)
  frameHi := (1477660790031 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12661]
  agentFrame_pos := by norm_num only [agent12661]
  worldRadius := (2162822499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12661]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1507773239 / 1000000000000 : ℝ)
  lowerTail := (444435187 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8291084971 / 1000000000000 : ℝ)
  ledger := by
    have h : (293435731 / 250000000000 : ℚ) +
        (9508482537 / 1000000000000000000 : ℚ) / (2162822499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1507773239 / 1000000000000 : ℚ) + (444435187 / 250000000000 : ℚ) ≤
        (8291084971 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((293435731 / 250000000000 : ℚ) +
        (9508482537 / 1000000000000000000 : ℚ) / (2162822499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1507773239 / 1000000000000 : ℚ) + (444435187 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8291084971 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12661]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12661 :
    2 * 160 < 12661 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999887 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12661 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12662 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12662. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12662 : WorldParameters where
  hiddenCharge := (117369887 / 100000000000 : ℝ)
  frame := (25046174489 / 40000000000 : ℝ)
  moment := (9506519843 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12662 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147762820397 / 100000000000 : ℝ)
    root := (1704319041 / 200000000000 : ℝ) }

noncomputable def scalar12662 : ScalarCertificate 12662 world12662 agent12662 where
  dimensionLo := 12662
  dimensionHi := 12662
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2163178999 / 1000000000000 : ℝ)
  frameLo := (25046174489 / 40000000000 : ℝ)
  frameHi := (147762820397 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12662]
  agentFrame_pos := by norm_num only [agent12662]
  worldRadius := (2163178999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12662]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (376622551 / 250000000000 : ℝ)
  lowerTail := (222041987 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8287263661 / 1000000000000 : ℝ)
  ledger := by
    have h : (117369887 / 100000000000 : ℚ) +
        (9506519843 / 1000000000000000000 : ℚ) / (2163178999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (376622551 / 250000000000 : ℚ) + (222041987 / 125000000000 : ℚ) ≤
        (8287263661 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((117369887 / 100000000000 : ℚ) +
        (9506519843 / 1000000000000000000 : ℚ) / (2163178999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (376622551 / 250000000000 : ℚ) + (222041987 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8287263661 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12662]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12662 :
    2 * 160 < 12662 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999817 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12662 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12663 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12663. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12663 : WorldParameters where
  hiddenCharge := (1173654827 / 1000000000000 : ℝ)
  frame := (626140435243 / 1000000000000 : ℝ)
  moment := (4752278857 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12663 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (36939890961 / 25000000000 : ℝ)
    root := (1065113077 / 125000000000 : ℝ) }

noncomputable def scalar12663 : ScalarCertificate 12663 world12663 agent12663 where
  dimensionLo := 12663
  dimensionHi := 12663
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2163535799 / 1000000000000 : ℝ)
  frameLo := (626140435243 / 1000000000000 : ℝ)
  frameHi := (36939890961 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12663]
  agentFrame_pos := by norm_num only [agent12663]
  worldRadius := (2163535799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12663]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1505208721 / 1000000000000 : ℝ)
  lowerTail := (354986533 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8283445699 / 1000000000000 : ℝ)
  ledger := by
    have h : (1173654827 / 1000000000000 : ℚ) +
        (4752278857 / 500000000000000000 : ℚ) / (2163535799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1505208721 / 1000000000000 : ℚ) + (354986533 / 200000000000 : ℚ) ≤
        (8283445699 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1173654827 / 1000000000000 : ℚ) +
        (4752278857 / 500000000000000000 : ℚ) / (2163535799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1505208721 / 1000000000000 : ℚ) + (354986533 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8283445699 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12663]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12663 :
    2 * 160 < 12663 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999547 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12663 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12664 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12664. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12664 : WorldParameters where
  hiddenCharge := (293402699 / 250000000000 : ℝ)
  frame := (626126510503 / 1000000000000 : ℝ)
  moment := (1187824519 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12664 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (738781543753 / 500000000000 : ℝ)
    root := (1704042849 / 200000000000 : ℝ) }

noncomputable def scalar12664 : ScalarCertificate 12664 world12664 agent12664 where
  dimensionLo := 12664
  dimensionHi := 12664
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2163892299 / 1000000000000 : ℝ)
  frameLo := (626126510503 / 1000000000000 : ℝ)
  frameHi := (738781543753 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12664]
  agentFrame_pos := by norm_num only [agent12664]
  worldRadius := (2163892299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12664]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1503928223 / 1000000000000 : ℝ)
  lowerTail := (27711413 / 15625000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (517476939 / 62500000000 : ℝ)
  ledger := by
    have h : (293402699 / 250000000000 : ℚ) +
        (1187824519 / 125000000000000000 : ℚ) / (2163892299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1503928223 / 1000000000000 : ℚ) + (27711413 / 15625000000 : ℚ) ≤
        (517476939 / 62500000000 : ℚ) := by norm_num only
    have hc : (((293402699 / 250000000000 : ℚ) +
        (1187824519 / 125000000000000000 : ℚ) / (2163892299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1503928223 / 1000000000000 : ℚ) + (27711413 / 15625000000 : ℚ) : ℚ) : ℝ) ≤
        ((517476939 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12664]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12664 :
    2 * 160 < 12664 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (27499993 / 2500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12664 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12665 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12665. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12665 : WorldParameters where
  hiddenCharge := (1173566777 / 1000000000000 : ℝ)
  frame := (156528147001 / 250000000000 : ℝ)
  moment := (1900127031 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12665 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1477530557083 / 1000000000000 : ℝ)
    root := (8519524159 / 1000000000000 : ℝ) }

noncomputable def scalar12665 : ScalarCertificate 12665 world12665 agent12665 where
  dimensionLo := 12665
  dimensionHi := 12665
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2164248899 / 1000000000000 : ℝ)
  frameLo := (156528147001 / 250000000000 : ℝ)
  frameHi := (1477530557083 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12665]
  agentFrame_pos := by norm_num only [agent12665]
  worldRadius := (2164248899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12665]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (751324577 / 500000000000 : ℝ)
  lowerTail := (22151621 / 12500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (827581981 / 100000000000 : ℝ)
  ledger := by
    have h : (1173566777 / 1000000000000 : ℚ) +
        (1900127031 / 200000000000000000 : ℚ) / (2164248899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (751324577 / 500000000000 : ℚ) + (22151621 / 12500000000 : ℚ) ≤
        (827581981 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1173566777 / 1000000000000 : ℚ) +
        (1900127031 / 200000000000000000 : ℚ) / (2164248899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (751324577 / 500000000000 : ℚ) + (22151621 / 12500000000 : ℚ) : ℚ) : ℝ) ≤
        ((827581981 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12665]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12665 :
    2 * 160 < 12665 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998897 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12665 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12666 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12666. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12666 : WorldParameters where
  hiddenCharge := (1173522769 / 1000000000000 : ℝ)
  frame := (626098667747 / 1000000000000 : ℝ)
  moment := (2374668681 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12666 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369374510309 / 250000000000 : ℝ)
    root := (532427139 / 62500000000 : ℝ) }

noncomputable def scalar12666 : ScalarCertificate 12666 world12666 agent12666 where
  dimensionLo := 12666
  dimensionHi := 12666
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2164605599 / 1000000000000 : ℝ)
  frameLo := (626098667747 / 1000000000000 : ℝ)
  frameHi := (369374510309 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12666]
  agentFrame_pos := by norm_num only [agent12666]
  worldRadius := (2164605599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12666]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (750685683 / 500000000000 : ℝ)
  lowerTail := (354146051 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2068002939 / 250000000000 : ℝ)
  ledger := by
    have h : (1173522769 / 1000000000000 : ℚ) +
        (2374668681 / 250000000000000000 : ℚ) / (2164605599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (750685683 / 500000000000 : ℚ) + (354146051 / 200000000000 : ℚ) ≤
        (2068002939 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1173522769 / 1000000000000 : ℚ) +
        (2374668681 / 250000000000000000 : ℚ) / (2164605599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (750685683 / 500000000000 : ℚ) + (354146051 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2068002939 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12666]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12666 :
    2 * 160 < 12666 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999529 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12666 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12667 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12667. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12667 : WorldParameters where
  hiddenCharge := (586739387 / 500000000000 : ℝ)
  frame := (626084749731 / 1000000000000 : ℝ)
  moment := (9496714857 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12667 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1477465545881 / 1000000000000 : ℝ)
    root := (8518144507 / 1000000000000 : ℝ) }

noncomputable def scalar12667 : ScalarCertificate 12667 world12667 agent12667 where
  dimensionLo := 12667
  dimensionHi := 12667
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2164962299 / 1000000000000 : ℝ)
  frameLo := (626084749731 / 1000000000000 : ℝ)
  frameHi := (1477465545881 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12667]
  agentFrame_pos := by norm_num only [agent12667]
  worldRadius := (2164962299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12667]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (750047427 / 500000000000 : ℝ)
  lowerTail := (1769332151 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8268207039 / 1000000000000 : ℝ)
  ledger := by
    have h : (586739387 / 500000000000 : ℚ) +
        (9496714857 / 1000000000000000000 : ℚ) / (2164962299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (750047427 / 500000000000 : ℚ) + (1769332151 / 1000000000000 : ℚ) ≤
        (8268207039 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((586739387 / 500000000000 : ℚ) +
        (9496714857 / 1000000000000000000 : ℚ) / (2164962299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (750047427 / 500000000000 : ℚ) + (1769332151 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8268207039 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12667]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12667 :
    2 * 160 < 12667 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997217 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12667 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12668 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12668. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12668 : WorldParameters where
  hiddenCharge := (1173434789 / 1000000000000 : ℝ)
  frame := (313035416977 / 500000000000 : ℝ)
  moment := (2373688889 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12668 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (295486614201 / 200000000000 : ℝ)
    root := (8517455007 / 1000000000000 : ℝ) }

noncomputable def scalar12668 : ScalarCertificate 12668 world12668 agent12668 where
  dimensionLo := 12668
  dimensionHi := 12668
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2165318899 / 1000000000000 : ℝ)
  frameLo := (313035416977 / 500000000000 : ℝ)
  frameHi := (295486614201 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12668]
  agentFrame_pos := by norm_num only [agent12668]
  worldRadius := (2165318899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12668]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1498819529 / 1000000000000 : ℝ)
  lowerTail := (1767935269 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2066101413 / 250000000000 : ℝ)
  ledger := by
    have h : (1173434789 / 1000000000000 : ℚ) +
        (2373688889 / 250000000000000000 : ℚ) / (2165318899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1498819529 / 1000000000000 : ℚ) + (1767935269 / 1000000000000 : ℚ) ≤
        (2066101413 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1173434789 / 1000000000000 : ℚ) +
        (2373688889 / 250000000000000000 : ℚ) / (2165318899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1498819529 / 1000000000000 : ℚ) + (1767935269 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2066101413 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12668]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12668 :
    2 * 160 < 12668 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (439999771 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12668 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12669 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12669. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12669 : WorldParameters where
  hiddenCharge := (1173390817 / 1000000000000 : ℝ)
  frame := (626056920417 / 1000000000000 : ℝ)
  moment := (474639841 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12669 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369350152669 / 250000000000 : ℝ)
    root := (340670629 / 40000000000 : ℝ) }

noncomputable def scalar12669 : ScalarCertificate 12669 world12669 agent12669 where
  dimensionLo := 12669
  dimensionHi := 12669
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2165675499 / 1000000000000 : ℝ)
  frameLo := (626056920417 / 1000000000000 : ℝ)
  frameHi := (369350152669 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12669]
  agentFrame_pos := by norm_num only [agent12669]
  worldRadius := (2165675499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12669]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (29950909 / 20000000000 : ℝ)
  lowerTail := (1766539671 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4130303767 / 500000000000 : ℝ)
  ledger := by
    have h : (1173390817 / 1000000000000 : ℚ) +
        (474639841 / 50000000000000000 : ℚ) / (2165675499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (29950909 / 20000000000 : ℚ) + (1766539671 / 1000000000000 : ℚ) ≤
        (4130303767 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1173390817 / 1000000000000 : ℚ) +
        (474639841 / 50000000000000000 : ℚ) / (2165675499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (29950909 / 20000000000 : ℚ) + (1766539671 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4130303767 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12669]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12669 :
    2 * 160 < 12669 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994933 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12669 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12670 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12670. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12670 : WorldParameters where
  hiddenCharge := (146668357 / 125000000000 : ℝ)
  frame := (626043009119 / 1000000000000 : ℝ)
  moment := (1186354831 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12670 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (738643236277 / 500000000000 : ℝ)
    root := (425803833 / 50000000000 : ℝ) }

noncomputable def scalar12670 : ScalarCertificate 12670 world12670 agent12670 where
  dimensionLo := 12670
  dimensionHi := 12670
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2166144099 / 1000000000000 : ℝ)
  frameLo := (626043009119 / 1000000000000 : ℝ)
  frameHi := (738643236277 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12670]
  agentFrame_pos := by norm_num only [agent12670]
  worldRadius := (2166144099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12670]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1496001923 / 1000000000000 : ℝ)
  lowerTail := (441199391 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4127992507 / 500000000000 : ℝ)
  ledger := by
    have h : (146668357 / 125000000000 : ℚ) +
        (1186354831 / 125000000000000000 : ℚ) / (2166144099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1496001923 / 1000000000000 : ℚ) + (441199391 / 250000000000 : ℚ) ≤
        (4127992507 / 500000000000 : ℚ) := by norm_num only
    have hc : (((146668357 / 125000000000 : ℚ) +
        (1186354831 / 125000000000000000 : ℚ) / (2166144099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1496001923 / 1000000000000 : ℚ) + (441199391 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4127992507 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12670]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12670 :
    2 * 160 < 12670 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999917 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12670 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12671 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12671. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12671 : WorldParameters where
  hiddenCharge := (1173302907 / 1000000000000 : ℝ)
  frame := (626029100059 / 1000000000000 : ℝ)
  moment := (118611013 / 12500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12671 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (738627027049 / 500000000000 : ℝ)
    root := (212884697 / 25000000000 : ℝ) }

noncomputable def scalar12671 : ScalarCertificate 12671 world12671 agent12671 where
  dimensionLo := 12671
  dimensionHi := 12671
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2166500799 / 1000000000000 : ℝ)
  frameLo := (626029100059 / 1000000000000 : ℝ)
  frameHi := (738627027049 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12671]
  agentFrame_pos := by norm_num only [agent12671]
  worldRadius := (2166500799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12671]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (59789229 / 40000000000 : ℝ)
  lowerTail := (88170249 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8252194223 / 1000000000000 : ℝ)
  ledger := by
    have h : (1173302907 / 1000000000000 : ℚ) +
        (118611013 / 12500000000000000 : ℚ) / (2166500799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (59789229 / 40000000000 : ℚ) + (88170249 / 50000000000 : ℚ) ≤
        (8252194223 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1173302907 / 1000000000000 : ℚ) +
        (118611013 / 12500000000000000 : ℚ) / (2166500799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (59789229 / 40000000000 : ℚ) + (88170249 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8252194223 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12671]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12671 :
    2 * 160 < 12671 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994679 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12671 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12672 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12672. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12672 : WorldParameters where
  hiddenCharge := (1173258969 / 1000000000000 : ℝ)
  frame := (626015193237 / 1000000000000 : ℝ)
  moment := (9486923997 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12672 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369305411059 / 250000000000 : ℝ)
    root := (8514699249 / 1000000000000 : ℝ) }

noncomputable def scalar12672 : ScalarCertificate 12672 world12672 agent12672 where
  dimensionLo := 12672
  dimensionHi := 12672
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2166857399 / 1000000000000 : ℝ)
  frameLo := (626015193237 / 1000000000000 : ℝ)
  frameHi := (369305411059 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12672]
  agentFrame_pos := by norm_num only [agent12672]
  worldRadius := (2166857399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12672]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (298692119 / 200000000000 : ℝ)
  lowerTail := (881006743 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8248406511 / 1000000000000 : ℝ)
  ledger := by
    have h : (1173258969 / 1000000000000 : ℚ) +
        (9486923997 / 1000000000000000000 : ℚ) / (2166857399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (298692119 / 200000000000 : ℚ) + (881006743 / 500000000000 : ℚ) ≤
        (8248406511 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1173258969 / 1000000000000 : ℚ) +
        (9486923997 / 1000000000000000000 : ℚ) / (2166857399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (298692119 / 200000000000 : ℚ) + (881006743 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8248406511 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12672]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12672 :
    2 * 160 < 12672 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999931 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12672 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12673 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12673. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12673 : WorldParameters where
  hiddenCharge := (1173215043 / 1000000000000 : ℝ)
  frame := (156500322163 / 250000000000 : ℝ)
  moment := (4742483759 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12673 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (59087570429 / 40000000000 : ℝ)
    root := (1702802167 / 200000000000 : ℝ) }

noncomputable def scalar12673 : ScalarCertificate 12673 world12673 agent12673 where
  dimensionLo := 12673
  dimensionHi := 12673
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2167214099 / 1000000000000 : ℝ)
  frameLo := (156500322163 / 250000000000 : ℝ)
  frameHi := (59087570429 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12673]
  agentFrame_pos := by norm_num only [agent12673]
  worldRadius := (2167214099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12673]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (186523981 / 125000000000 : ℝ)
  lowerTail := (352124687 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8244622173 / 1000000000000 : ℝ)
  ledger := by
    have h : (1173215043 / 1000000000000 : ℚ) +
        (4742483759 / 500000000000000000 : ℚ) / (2167214099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (186523981 / 125000000000 : ℚ) + (352124687 / 200000000000 : ℚ) ≤
        (8244622173 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1173215043 / 1000000000000 : ℚ) +
        (4742483759 / 500000000000000000 : ℚ) / (2167214099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (186523981 / 125000000000 : ℚ) + (352124687 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8244622173 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12673]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12673 :
    2 * 160 < 12673 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999533 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12673 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12674 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12674. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12674 : WorldParameters where
  hiddenCharge := (1173171129 / 1000000000000 : ℝ)
  frame := (9781052911 / 15625000000 : ℝ)
  moment := (4741505801 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12674 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1477156891711 / 1000000000000 : ℝ)
    root := (4256661319 / 500000000000 : ℝ) }

noncomputable def scalar12674 : ScalarCertificate 12674 world12674 agent12674 where
  dimensionLo := 12674
  dimensionHi := 12674
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2167570799 / 1000000000000 : ℝ)
  frameLo := (9781052911 / 15625000000 : ℝ)
  frameHi := (1477156891711 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12674]
  agentFrame_pos := by norm_num only [agent12674]
  worldRadius := (2167570799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12674]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (74546217 / 50000000000 : ℝ)
  lowerTail := (87961733 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4120420543 / 500000000000 : ℝ)
  ledger := by
    have h : (1173171129 / 1000000000000 : ℚ) +
        (4741505801 / 500000000000000000 : ℚ) / (2167570799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (74546217 / 50000000000 : ℚ) + (87961733 / 50000000000 : ℚ) ≤
        (4120420543 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1173171129 / 1000000000000 : ℚ) +
        (4741505801 / 500000000000000000 : ℚ) / (2167570799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (74546217 / 50000000000 : ℚ) + (87961733 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4120420543 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12674]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12674 :
    2 * 160 < 12674 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (219999923 / 20000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12674 {← IO.monoMsNow}" : IO Unit)
