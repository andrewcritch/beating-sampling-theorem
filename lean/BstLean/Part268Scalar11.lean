import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12625 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12625. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12625 : WorldParameters where
  hiddenCharge := (587668353 / 500000000000 : ℝ)
  frame := (313335621119 / 500000000000 : ℝ)
  moment := (299359947 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12625 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (92448034027 / 62500000000 : ℝ)
    root := (4273650477 / 500000000000 : ℝ) }

noncomputable def scalar12625 : ScalarCertificate 12625 world12625 agent12625 where
  dimensionLo := 12625
  dimensionHi := 12625
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2149549799 / 1000000000000 : ℝ)
  frameLo := (313335621119 / 500000000000 : ℝ)
  frameHi := (92448034027 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12625]
  agentFrame_pos := by norm_num only [agent12625]
  worldRadius := (2149549799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12625]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1555926857 / 1000000000000 : ℝ)
  lowerTail := (1830618149 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2108565817 / 250000000000 : ℝ)
  ledger := by
    have h : (587668353 / 500000000000 : ℚ) +
        (299359947 / 31250000000000000 : ℚ) / (2149549799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1555926857 / 1000000000000 : ℚ) + (1830618149 / 1000000000000 : ℚ) ≤
        (2108565817 / 250000000000 : ℚ) := by norm_num only
    have hc : (((587668353 / 500000000000 : ℚ) +
        (299359947 / 31250000000000000 : ℚ) / (2149549799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1555926857 / 1000000000000 : ℚ) + (1830618149 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2108565817 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12625]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12625 :
    2 * 160 < 12625 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999069 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12625 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12626 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12626. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12626 : WorldParameters where
  hiddenCharge := (1175292227 / 1000000000000 : ℝ)
  frame := (313328615941 / 500000000000 : ℝ)
  moment := (9577535091 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12626 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (92445976489 / 62500000000 : ℝ)
    root := (4273301093 / 500000000000 : ℝ) }

noncomputable def scalar12626 : ScalarCertificate 12626 world12626 agent12626 where
  dimensionLo := 12626
  dimensionHi := 12626
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2149905799 / 1000000000000 : ℝ)
  frameLo := (313328615941 / 500000000000 : ℝ)
  frameHi := (92445976489 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12626]
  agentFrame_pos := by norm_num only [agent12626]
  worldRadius := (2149905799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12626]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (48581167 / 31250000000 : ℝ)
  lowerTail := (914582757 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4215160509 / 500000000000 : ℝ)
  ledger := by
    have h : (1175292227 / 1000000000000 : ℚ) +
        (9577535091 / 1000000000000000000 : ℚ) / (2149905799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (48581167 / 31250000000 : ℚ) + (914582757 / 500000000000 : ℚ) ≤
        (4215160509 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1175292227 / 1000000000000 : ℚ) +
        (9577535091 / 1000000000000000000 : ℚ) / (2149905799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (48581167 / 31250000000 : ℚ) + (914582757 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4215160509 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12626]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12626 :
    2 * 160 < 12626 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996187 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12626 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12627 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12627. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12627 : WorldParameters where
  hiddenCharge := (1175247761 / 1000000000000 : ℝ)
  frame := (626643223789 / 1000000000000 : ℝ)
  moment := (2393888113 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12627 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147910271817 / 100000000000 : ℝ)
    root := (8545903641 / 1000000000000 : ℝ) }

noncomputable def scalar12627 : ScalarCertificate 12627 world12627 agent12627 where
  dimensionLo := 12627
  dimensionHi := 12627
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2150261699 / 1000000000000 : ℝ)
  frameLo := (626643223789 / 1000000000000 : ℝ)
  frameHi := (147910271817 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12627]
  agentFrame_pos := by norm_num only [agent12627]
  worldRadius := (2150261699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12627]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (194158631 / 125000000000 : ℝ)
  lowerTail := (1827714123 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4213191091 / 500000000000 : ℝ)
  ledger := by
    have h : (1175247761 / 1000000000000 : ℚ) +
        (2393888113 / 250000000000000000 : ℚ) / (2150261699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (194158631 / 125000000000 : ℚ) + (1827714123 / 1000000000000 : ℚ) ≤
        (4213191091 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1175247761 / 1000000000000 : ℚ) +
        (2393888113 / 250000000000000000 : ℚ) / (2150261699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (194158631 / 125000000000 : ℚ) + (1827714123 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4213191091 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12627]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12627 :
    2 * 160 < 12627 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996877 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12627 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12628 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12628. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12628 : WorldParameters where
  hiddenCharge := (1175203307 / 1000000000000 : ℝ)
  frame := (15665730449 / 25000000000 : ℝ)
  moment := (4786785193 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12628 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (739534916697 / 500000000000 : ℝ)
    root := (2136301347 / 250000000000 : ℝ) }

noncomputable def scalar12628 : ScalarCertificate 12628 world12628 agent12628 where
  dimensionLo := 12628
  dimensionHi := 12628
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2150617699 / 1000000000000 : ℝ)
  frameLo := (15665730449 / 25000000000 : ℝ)
  frameHi := (739534916697 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12628]
  agentFrame_pos := by norm_num only [agent12628]
  worldRadius := (2150617699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12628]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1551942241 / 1000000000000 : ℝ)
  lowerTail := (1826264273 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (263201467 / 31250000000 : ℝ)
  ledger := by
    have h : (1175203307 / 1000000000000 : ℚ) +
        (4786785193 / 500000000000000000 : ℚ) / (2150617699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1551942241 / 1000000000000 : ℚ) + (1826264273 / 1000000000000 : ℚ) ≤
        (263201467 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1175203307 / 1000000000000 : ℚ) +
        (4786785193 / 500000000000000000 : ℚ) / (2150617699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1551942241 / 1000000000000 : ℚ) + (1826264273 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((263201467 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12628]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12628 :
    2 * 160 < 12628 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (549999749 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12628 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12629 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12629. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12629 : WorldParameters where
  hiddenCharge := (73447429 / 62500000000 : ℝ)
  frame := (626615214393 / 1000000000000 : ℝ)
  moment := (4785794447 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12629 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1479036963553 / 1000000000000 : ℝ)
    root := (8544507291 / 1000000000000 : ℝ) }

noncomputable def scalar12629 : ScalarCertificate 12629 world12629 agent12629 where
  dimensionLo := 12629
  dimensionHi := 12629
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2150973599 / 1000000000000 : ℝ)
  frameLo := (626615214393 / 1000000000000 : ℝ)
  frameHi := (1479036963553 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12629]
  agentFrame_pos := by norm_num only [agent12629]
  worldRadius := (2150973599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12629]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (310123317 / 200000000000 : ℝ)
  lowerTail := (912407801 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2104628747 / 250000000000 : ℝ)
  ledger := by
    have h : (73447429 / 62500000000 : ℚ) +
        (4785794447 / 500000000000000000 : ℚ) / (2150973599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (310123317 / 200000000000 : ℚ) + (912407801 / 500000000000 : ℚ) ≤
        (2104628747 / 250000000000 : ℚ) := by norm_num only
    have hc : (((73447429 / 62500000000 : ℚ) +
        (4785794447 / 500000000000000000 : ℚ) / (2150973599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (310123317 / 200000000000 : ℚ) + (912407801 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2104628747 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12629]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12629 :
    2 * 160 < 12629 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996609 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12629 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12630 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12630. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12630 : WorldParameters where
  hiddenCharge := (1175114433 / 1000000000000 : ℝ)
  frame := (19581287909 / 31250000000 : ℝ)
  moment := (382784319 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12630 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (184865243253 / 125000000000 : ℝ)
    root := (1708761897 / 200000000000 : ℝ) }

noncomputable def scalar12630 : ScalarCertificate 12630 world12630 agent12630 where
  dimensionLo := 12630
  dimensionHi := 12630
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2151440999 / 1000000000000 : ℝ)
  frameLo := (19581287909 / 31250000000 : ℝ)
  frameHi := (184865243253 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12630]
  agentFrame_pos := by norm_num only [agent12630]
  worldRadius := (2151440999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12630]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (154901131 / 100000000000 : ℝ)
  lowerTail := (1823008251 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4206865591 / 500000000000 : ℝ)
  ledger := by
    have h : (1175114433 / 1000000000000 : ℚ) +
        (382784319 / 40000000000000000 : ℚ) / (2151440999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (154901131 / 100000000000 : ℚ) + (1823008251 / 1000000000000 : ℚ) ≤
        (4206865591 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1175114433 / 1000000000000 : ℚ) +
        (382784319 / 40000000000000000 : ℚ) / (2151440999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (154901131 / 100000000000 : ℚ) + (1823008251 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4206865591 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12630]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12630 :
    2 * 160 < 12630 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995603 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12630 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12631 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12631. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12631 : WorldParameters where
  hiddenCharge := (587535007 / 500000000000 : ℝ)
  frame := (125317442809 / 200000000000 : ℝ)
  moment := (2391906907 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12631 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369722278231 / 250000000000 : ℝ)
    root := (4271555917 / 500000000000 : ℝ) }

noncomputable def scalar12631 : ScalarCertificate 12631 world12631 agent12631 where
  dimensionLo := 12631
  dimensionHi := 12631
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2151797099 / 1000000000000 : ℝ)
  frameLo := (125317442809 / 200000000000 : ℝ)
  frameHi := (369722278231 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12631]
  agentFrame_pos := by norm_num only [agent12631]
  worldRadius := (2151797099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12631]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (154768867 / 100000000000 : ℝ)
  lowerTail := (1821562729 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4204903337 / 500000000000 : ℝ)
  ledger := by
    have h : (587535007 / 500000000000 : ℚ) +
        (2391906907 / 250000000000000000 : ℚ) / (2151797099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (154768867 / 100000000000 : ℚ) + (1821562729 / 1000000000000 : ℚ) ≤
        (4204903337 / 500000000000 : ℚ) := by norm_num only
    have hc : (((587535007 / 500000000000 : ℚ) +
        (2391906907 / 250000000000000000 : ℚ) / (2151797099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (154768867 / 100000000000 : ℚ) + (1821562729 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4204903337 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12631]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12631 :
    2 * 160 < 12631 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998077 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12631 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12632 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12632. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12632 : WorldParameters where
  hiddenCharge := (1175025607 / 1000000000000 : ℝ)
  frame := (313286608631 / 500000000000 : ℝ)
  moment := (4782823927 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12632 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1478856300659 / 1000000000000 : ℝ)
    root := (4271207237 / 500000000000 : ℝ) }

noncomputable def scalar12632 : ScalarCertificate 12632 world12632 agent12632 where
  dimensionLo := 12632
  dimensionHi := 12632
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2152152899 / 1000000000000 : ℝ)
  frameLo := (313286608631 / 500000000000 : ℝ)
  frameHi := (1478856300659 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12632]
  agentFrame_pos := by norm_num only [agent12632]
  worldRadius := (2152152899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12632]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (193295893 / 125000000000 : ℝ)
  lowerTail := (1820118339 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8405885747 / 1000000000000 : ℝ)
  ledger := by
    have h : (1175025607 / 1000000000000 : ℚ) +
        (4782823927 / 500000000000000000 : ℚ) / (2152152899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (193295893 / 125000000000 : ℚ) + (1820118339 / 1000000000000 : ℚ) ≤
        (8405885747 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1175025607 / 1000000000000 : ℚ) +
        (4782823927 / 500000000000000000 : ℚ) / (2152152899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (193295893 / 125000000000 : ℚ) + (1820118339 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8405885747 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12632]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12632 :
    2 * 160 < 12632 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997867 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12632 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12633 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12633. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12633 : WorldParameters where
  hiddenCharge := (293745303 / 250000000000 : ℝ)
  frame := (31327961137 / 50000000000 : ℝ)
  moment := (9563668653 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12633 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (739411754609 / 500000000000 : ℝ)
    root := (8541717269 / 1000000000000 : ℝ) }

noncomputable def scalar12633 : ScalarCertificate 12633 world12633 agent12633 where
  dimensionLo := 12633
  dimensionHi := 12633
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2152508999 / 1000000000000 : ℝ)
  frameLo := (31327961137 / 50000000000 : ℝ)
  frameHi := (739411754609 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12633]
  agentFrame_pos := by norm_num only [agent12633]
  worldRadius := (2152508999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12633]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1545047159 / 1000000000000 : ℝ)
  lowerTail := (1818675557 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (168039363 / 20000000000 : ℝ)
  ledger := by
    have h : (293745303 / 250000000000 : ℚ) +
        (9563668653 / 1000000000000000000 : ℚ) / (2152508999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1545047159 / 1000000000000 : ℚ) + (1818675557 / 1000000000000 : ℚ) ≤
        (168039363 / 20000000000 : ℚ) := by norm_num only
    have hc : (((293745303 / 250000000000 : ℚ) +
        (9563668653 / 1000000000000000000 : ℚ) / (2152508999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1545047159 / 1000000000000 : ℚ) + (1818675557 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((168039363 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12633]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12633 :
    2 * 160 < 12633 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994947 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12633 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12634 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12634. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12634 : WorldParameters where
  hiddenCharge := (293734207 / 250000000000 : ℝ)
  frame := (313272615239 / 500000000000 : ℝ)
  moment := (9561690023 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12634 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (739395366329 / 500000000000 : ℝ)
    root := (8541020287 / 1000000000000 : ℝ) }

noncomputable def scalar12634 : ScalarCertificate 12634 world12634 agent12634 where
  dimensionLo := 12634
  dimensionHi := 12634
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2152864999 / 1000000000000 : ℝ)
  frameLo := (313272615239 / 500000000000 : ℝ)
  frameHi := (739395366329 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12634]
  agentFrame_pos := by norm_num only [agent12634]
  worldRadius := (2152864999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12634]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (77186419 / 50000000000 : ℝ)
  lowerTail := (1817234009 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8398053943 / 1000000000000 : ℝ)
  ledger := by
    have h : (293734207 / 250000000000 : ℚ) +
        (9561690023 / 1000000000000000000 : ℚ) / (2152864999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (77186419 / 50000000000 : ℚ) + (1817234009 / 1000000000000 : ℚ) ≤
        (8398053943 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((293734207 / 250000000000 : ℚ) +
        (9561690023 / 1000000000000000000 : ℚ) / (2152864999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (77186419 / 50000000000 : ℚ) + (1817234009 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8398053943 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12634]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12634 :
    2 * 160 < 12634 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995439 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12634 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12635 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12635. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12635 : WorldParameters where
  hiddenCharge := (146861557 / 125000000000 : ℝ)
  frame := (25061249619 / 40000000000 : ℝ)
  moment := (4779855983 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12635 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147875797097 / 100000000000 : ℝ)
    root := (1708064719 / 200000000000 : ℝ) }

noncomputable def scalar12635 : ScalarCertificate 12635 world12635 agent12635 where
  dimensionLo := 12635
  dimensionHi := 12635
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2153220999 / 1000000000000 : ℝ)
  frameLo := (25061249619 / 40000000000 : ℝ)
  frameHi := (147875797097 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12635]
  agentFrame_pos := by norm_num only [agent12635]
  worldRadius := (2153220999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12635]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1542410959 / 1000000000000 : ℝ)
  lowerTail := (1815793857 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2098535811 / 250000000000 : ℝ)
  ledger := by
    have h : (146861557 / 125000000000 : ℚ) +
        (4779855983 / 500000000000000000 : ℚ) / (2153220999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1542410959 / 1000000000000 : ℚ) + (1815793857 / 1000000000000 : ℚ) ≤
        (2098535811 / 250000000000 : ℚ) := by norm_num only
    have hc : (((146861557 / 125000000000 : ℚ) +
        (4779855983 / 500000000000000000 : ℚ) / (2153220999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1542410959 / 1000000000000 : ℚ) + (1815793857 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2098535811 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12635]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12635 :
    2 * 160 < 12635 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999661 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12635 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12636 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12636. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12636 : WorldParameters where
  hiddenCharge := (36714003 / 31250000000 : ℝ)
  frame := (62651725273 / 100000000000 : ℝ)
  moment := (119471681 / 12500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12636 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (739362618003 / 500000000000 : ℝ)
    root := (4269813529 / 500000000000 : ℝ) }

noncomputable def scalar12636 : ScalarCertificate 12636 world12636 agent12636 where
  dimensionLo := 12636
  dimensionHi := 12636
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2153576999 / 1000000000000 : ℝ)
  frameLo := (62651725273 / 100000000000 : ℝ)
  frameHi := (739362618003 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12636]
  agentFrame_pos := by norm_num only [agent12636]
  worldRadius := (2153576999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12636]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (770547413 / 500000000000 : ℝ)
  lowerTail := (1814355041 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4195117963 / 500000000000 : ℝ)
  ledger := by
    have h : (36714003 / 31250000000 : ℚ) +
        (119471681 / 12500000000000000 : ℚ) / (2153576999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (770547413 / 500000000000 : ℚ) + (1814355041 / 1000000000000 : ℚ) ≤
        (4195117963 / 500000000000 : ℚ) := by norm_num only
    have hc : (((36714003 / 31250000000 : ℚ) +
        (119471681 / 12500000000000000 : ℚ) / (2153576999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (770547413 / 500000000000 : ℚ) + (1814355041 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4195117963 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12636]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12636 :
    2 * 160 < 12636 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (343749821 / 31250000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12636 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12637 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12637. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12637 : WorldParameters where
  hiddenCharge := (293700937 / 250000000000 : ℝ)
  frame := (156625816811 / 250000000000 : ℝ)
  moment := (4777878783 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12637 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (36967312749 / 25000000000 : ℝ)
    root := (8538930811 / 1000000000000 : ℝ) }

noncomputable def scalar12637 : ScalarCertificate 12637 world12637 agent12637 where
  dimensionLo := 12637
  dimensionHi := 12637
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2153933099 / 1000000000000 : ℝ)
  frameLo := (156625816811 / 250000000000 : ℝ)
  frameHi := (36967312749 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12637]
  agentFrame_pos := by norm_num only [agent12637]
  worldRadius := (2153933099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12637]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1539780111 / 1000000000000 : ℝ)
  lowerTail := (1812917683 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8386332047 / 1000000000000 : ℝ)
  ledger := by
    have h : (293700937 / 250000000000 : ℚ) +
        (4777878783 / 500000000000000000 : ℚ) / (2153933099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1539780111 / 1000000000000 : ℚ) + (1812917683 / 1000000000000 : ℚ) ≤
        (8386332047 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((293700937 / 250000000000 : ℚ) +
        (4777878783 / 500000000000000000 : ℚ) / (2153933099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1539780111 / 1000000000000 : ℚ) + (1812917683 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8386332047 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12637]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12637 :
    2 * 160 < 12637 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998719 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12637 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12638 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12638. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12638 : WorldParameters where
  hiddenCharge := (293689853 / 250000000000 : ℝ)
  frame := (313244642007 / 500000000000 : ℝ)
  moment := (9553781223 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12638 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1478659810617 / 1000000000000 : ℝ)
    root := (4269117359 / 500000000000 : ℝ) }

noncomputable def scalar12638 : ScalarCertificate 12638 world12638 agent12638 where
  dimensionLo := 12638
  dimensionHi := 12638
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2154289099 / 1000000000000 : ℝ)
  frameLo := (313244642007 / 500000000000 : ℝ)
  frameHi := (1478659810617 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12638]
  agentFrame_pos := by norm_num only [agent12638]
  worldRadius := (2154289099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12638]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (153846659 / 100000000000 : ℝ)
  lowerTail := (45287039 / 25000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4191215771 / 500000000000 : ℝ)
  ledger := by
    have h : (293689853 / 250000000000 : ℚ) +
        (9553781223 / 1000000000000000000 : ℚ) / (2154289099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (153846659 / 100000000000 : ℚ) + (45287039 / 25000000000 : ℚ) ≤
        (4191215771 / 500000000000 : ℚ) := by norm_num only
    have hc : (((293689853 / 250000000000 : ℚ) +
        (9553781223 / 1000000000000000000 : ℚ) / (2154289099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (153846659 / 100000000000 : ℚ) + (45287039 / 25000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4191215771 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12638]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12638 :
    2 * 160 < 12638 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994181 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12638 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12639 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12639. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12639 : WorldParameters where
  hiddenCharge := (1174715087 / 1000000000000 : ℝ)
  frame := (313237651521 / 500000000000 : ℝ)
  moment := (9551805451 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12639 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1478627120173 / 1000000000000 : ℝ)
    root := (8537538847 / 1000000000000 : ℝ) }

noncomputable def scalar12639 : ScalarCertificate 12639 world12639 agent12639 where
  dimensionLo := 12639
  dimensionHi := 12639
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2154645099 / 1000000000000 : ℝ)
  frameLo := (313237651521 / 500000000000 : ℝ)
  frameHi := (1478627120173 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12639]
  agentFrame_pos := by norm_num only [agent12639]
  worldRadius := (2154645099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12639]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (384288583 / 250000000000 : ℝ)
  lowerTail := (181004673 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8378534347 / 1000000000000 : ℝ)
  ledger := by
    have h : (1174715087 / 1000000000000 : ℚ) +
        (9551805451 / 1000000000000000000 : ℚ) / (2154645099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (384288583 / 250000000000 : ℚ) + (181004673 / 100000000000 : ℚ) ≤
        (8378534347 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1174715087 / 1000000000000 : ℚ) +
        (9551805451 / 1000000000000000000 : ℚ) / (2154645099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (384288583 / 250000000000 : ℚ) + (181004673 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8378534347 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12639]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12639 :
    2 * 160 < 12639 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999099 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12639 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12640 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12640. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12640 : WorldParameters where
  hiddenCharge := (46986831 / 40000000000 : ℝ)
  frame := (313230662163 / 500000000000 : ℝ)
  moment := (9549830251 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12640 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1478512407271 / 1000000000000 : ℝ)
    root := (4268421633 / 500000000000 : ℝ) }

noncomputable def scalar12640 : ScalarCertificate 12640 world12640 agent12640 where
  dimensionLo := 12640
  dimensionHi := 12640
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2155112599 / 1000000000000 : ℝ)
  frameLo := (313230662163 / 500000000000 : ℝ)
  frameHi := (1478512407271 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12640]
  agentFrame_pos := by norm_num only [agent12640]
  worldRadius := (2155112599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12640]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1535564969 / 1000000000000 : ℝ)
  lowerTail := (904128119 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8373792361 / 1000000000000 : ℝ)
  ledger := by
    have h : (46986831 / 40000000000 : ℚ) +
        (9549830251 / 1000000000000000000 : ℚ) / (2155112599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1535564969 / 1000000000000 : ℚ) + (904128119 / 500000000000 : ℚ) ≤
        (8373792361 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((46986831 / 40000000000 : ℚ) +
        (9549830251 / 1000000000000000000 : ℚ) / (2155112599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1535564969 / 1000000000000 : ℚ) + (904128119 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8373792361 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12640]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12640 :
    2 * 160 < 12640 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997491 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12640 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12641 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12641. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12641 : WorldParameters where
  hiddenCharge := (587313237 / 500000000000 : ℝ)
  frame := (125289469573 / 200000000000 : ℝ)
  moment := (477392781 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12641 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (739239879641 / 500000000000 : ℝ)
    root := (8536147839 / 1000000000000 : ℝ) }

noncomputable def scalar12641 : ScalarCertificate 12641 world12641 agent12641 where
  dimensionLo := 12641
  dimensionHi := 12641
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2155468599 / 1000000000000 : ℝ)
  frameLo := (125289469573 / 200000000000 : ℝ)
  frameHi := (739239879641 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12641]
  agentFrame_pos := by norm_num only [agent12641]
  worldRadius := (2155468599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12641]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1534255537 / 1000000000000 : ℝ)
  lowerTail := (1806824357 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2092475649 / 250000000000 : ℝ)
  ledger := by
    have h : (587313237 / 500000000000 : ℚ) +
        (477392781 / 50000000000000000 : ℚ) / (2155468599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1534255537 / 1000000000000 : ℚ) + (1806824357 / 1000000000000 : ℚ) ≤
        (2092475649 / 250000000000 : ℚ) := by norm_num only
    have hc : (((587313237 / 500000000000 : ℚ) +
        (477392781 / 50000000000000000 : ℚ) / (2155468599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1534255537 / 1000000000000 : ℚ) + (1806824357 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2092475649 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12641]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12641 :
    2 * 160 < 12641 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994119 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12641 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12642 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12642. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12642 : WorldParameters where
  hiddenCharge := (234916437 / 200000000000 : ℝ)
  frame := (31321668683 / 50000000000 : ℝ)
  moment := (9545881561 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12642 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1478447126093 / 1000000000000 : ℝ)
    root := (8535452633 / 1000000000000 : ℝ) }

noncomputable def scalar12642 : ScalarCertificate 12642 world12642 agent12642 where
  dimensionLo := 12642
  dimensionHi := 12642
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2155824699 / 1000000000000 : ℝ)
  frameLo := (31321668683 / 50000000000 : ℝ)
  frameHi := (1478447126093 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12642]
  agentFrame_pos := by norm_num only [agent12642]
  worldRadius := (2155824699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12642]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (766473741 / 500000000000 : ℝ)
  lowerTail := (1805393897 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8366016189 / 1000000000000 : ℝ)
  ledger := by
    have h : (234916437 / 200000000000 : ℚ) +
        (9545881561 / 1000000000000000000 : ℚ) / (2155824699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (766473741 / 500000000000 : ℚ) + (1805393897 / 1000000000000 : ℚ) ≤
        (8366016189 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((234916437 / 200000000000 : ℚ) +
        (9545881561 / 1000000000000000000 : ℚ) / (2155824699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (766473741 / 500000000000 : ℚ) + (1805393897 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8366016189 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12642]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12642 :
    2 * 160 < 12642 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999649 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12642 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12643 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12643. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12643 : WorldParameters where
  hiddenCharge := (1174537907 / 1000000000000 : ℝ)
  frame := (626419401709 / 1000000000000 : ℝ)
  moment := (9543908071 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12643 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (92400891907 / 62500000000 : ℝ)
    root := (2133689429 / 250000000000 : ℝ) }

noncomputable def scalar12643 : ScalarCertificate 12643 world12643 agent12643 where
  dimensionLo := 12643
  dimensionHi := 12643
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2156181099 / 1000000000000 : ℝ)
  frameLo := (626419401709 / 1000000000000 : ℝ)
  frameHi := (92400891907 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12643]
  agentFrame_pos := by norm_num only [agent12643]
  worldRadius := (2156181099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12643]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (382909987 / 250000000000 : ℝ)
  lowerTail := (225495471 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1672426163 / 200000000000 : ℝ)
  ledger := by
    have h : (1174537907 / 1000000000000 : ℚ) +
        (9543908071 / 1000000000000000000 : ℚ) / (2156181099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (382909987 / 250000000000 : ℚ) + (225495471 / 125000000000 : ℚ) ≤
        (1672426163 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1174537907 / 1000000000000 : ℚ) +
        (9543908071 / 1000000000000000000 : ℚ) / (2156181099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (382909987 / 250000000000 : ℚ) + (225495471 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1672426163 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12643]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12643 :
    2 * 160 < 12643 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999457 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12643 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12644 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12644. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12644 : WorldParameters where
  hiddenCharge := (587246821 / 500000000000 : ℝ)
  frame := (156601358003 / 250000000000 : ℝ)
  moment := (596370947 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12644 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (369595336679 / 250000000000 : ℝ)
    root := (8534062953 / 1000000000000 : ℝ) }

noncomputable def scalar12644 : ScalarCertificate 12644 world12644 agent12644 where
  dimensionLo := 12644
  dimensionHi := 12644
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2156537599 / 1000000000000 : ℝ)
  frameLo := (156601358003 / 250000000000 : ℝ)
  frameHi := (369595336679 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12644]
  agentFrame_pos := by norm_num only [agent12644]
  worldRadius := (2156537599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12644]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (47822917 / 31250000000 : ℝ)
  lowerTail := (72101381 / 40000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8358247819 / 1000000000000 : ℝ)
  ledger := by
    have h : (587246821 / 500000000000 : ℚ) +
        (596370947 / 62500000000000000 : ℚ) / (2156537599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (47822917 / 31250000000 : ℚ) + (72101381 / 40000000000 : ℚ) ≤
        (8358247819 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((587246821 / 500000000000 : ℚ) +
        (596370947 / 62500000000000000 : ℚ) / (2156537599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (47822917 / 31250000000 : ℚ) + (72101381 / 40000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8358247819 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12644]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12644 :
    2 * 160 < 12644 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (549999931 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12644 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12645 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12645. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12645 : WorldParameters where
  hiddenCharge := (293612347 / 250000000000 : ℝ)
  frame := (78298933071 / 125000000000 : ℝ)
  moment := (9539962803 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12645 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (36958711091 / 25000000000 : ℝ)
    root := (8533368411 / 1000000000000 : ℝ) }

noncomputable def scalar12645 : ScalarCertificate 12645 world12645 agent12645 where
  dimensionLo := 12645
  dimensionHi := 12645
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2156894199 / 1000000000000 : ℝ)
  frameLo := (78298933071 / 125000000000 : ℝ)
  frameHi := (36958711091 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12645]
  agentFrame_pos := by norm_num only [agent12645]
  worldRadius := (2156894199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12645]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1529028141 / 1000000000000 : ℝ)
  lowerTail := (900553367 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2088592059 / 250000000000 : ℝ)
  ledger := by
    have h : (293612347 / 250000000000 : ℚ) +
        (9539962803 / 1000000000000000000 : ℚ) / (2156894199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1529028141 / 1000000000000 : ℚ) + (900553367 / 500000000000 : ℚ) ≤
        (2088592059 / 250000000000 : ℚ) := by norm_num only
    have hc : (((293612347 / 250000000000 : ℚ) +
        (9539962803 / 1000000000000000000 : ℚ) / (2156894199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1529028141 / 1000000000000 : ℚ) + (900553367 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2088592059 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12645]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12645 :
    2 * 160 < 12645 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998041 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12645 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12646 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12646. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12646 : WorldParameters where
  hiddenCharge := (587202573 / 500000000000 : ℝ)
  frame := (626377499377 / 1000000000000 : ℝ)
  moment := (9537991023 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12646 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1478315561273 / 1000000000000 : ℝ)
    root := (8532674157 / 1000000000000 : ℝ) }

noncomputable def scalar12646 : ScalarCertificate 12646 world12646 agent12646 where
  dimensionLo := 12646
  dimensionHi := 12646
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2157250699 / 1000000000000 : ℝ)
  frameLo := (626377499377 / 1000000000000 : ℝ)
  frameHi := (1478315561273 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12646]
  agentFrame_pos := by norm_num only [agent12646]
  worldRadius := (2157250699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12646]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1527724217 / 1000000000000 : ℝ)
  lowerTail := (899840129 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8350492187 / 1000000000000 : ℝ)
  ledger := by
    have h : (587202573 / 500000000000 : ℚ) +
        (9537991023 / 1000000000000000000 : ℚ) / (2157250699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1527724217 / 1000000000000 : ℚ) + (899840129 / 500000000000 : ℚ) ≤
        (8350492187 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((587202573 / 500000000000 : ℚ) +
        (9537991023 / 1000000000000000000 : ℚ) / (2157250699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1527724217 / 1000000000000 : ℚ) + (899840129 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8350492187 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12646]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12646 :
    2 * 160 < 12646 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997761 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12646 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12647 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12647. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12647 : WorldParameters where
  hiddenCharge := (293590229 / 250000000000 : ℝ)
  frame := (313181768219 / 500000000000 : ℝ)
  moment := (2384004953 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12647 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (59131307747 / 40000000000 : ℝ)
    root := (1066497507 / 125000000000 : ℝ) }

noncomputable def scalar12647 : ScalarCertificate 12647 world12647 agent12647 where
  dimensionLo := 12647
  dimensionHi := 12647
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2157607199 / 1000000000000 : ℝ)
  frameLo := (313181768219 / 500000000000 : ℝ)
  frameHi := (59131307747 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12647]
  agentFrame_pos := by norm_num only [agent12647]
  worldRadius := (2157607199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12647]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1526421511 / 1000000000000 : ℝ)
  lowerTail := (1798255037 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4173309681 / 500000000000 : ℝ)
  ledger := by
    have h : (293590229 / 250000000000 : ℚ) +
        (2384004953 / 250000000000000000 : ℚ) / (2157607199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1526421511 / 1000000000000 : ℚ) + (1798255037 / 1000000000000 : ℚ) ≤
        (4173309681 / 500000000000 : ℚ) := by norm_num only
    have hc : (((293590229 / 250000000000 : ℚ) +
        (2384004953 / 250000000000000000 : ℚ) / (2157607199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1526421511 / 1000000000000 : ℚ) + (1798255037 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4173309681 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12647]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12647 :
    2 * 160 < 12647 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999641 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12647 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12648 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12648. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12648 : WorldParameters where
  hiddenCharge := (1174316697 / 1000000000000 : ℝ)
  frame := (626349575751 / 1000000000000 : ℝ)
  moment := (9534049171 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12648 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (739124923383 / 500000000000 : ℝ)
    root := (266602693 / 31250000000 : ℝ) }

noncomputable def scalar12648 : ScalarCertificate 12648 world12648 agent12648 where
  dimensionLo := 12648
  dimensionHi := 12648
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2157963699 / 1000000000000 : ℝ)
  frameLo := (626349575751 / 1000000000000 : ℝ)
  frameHi := (739124923383 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12648]
  agentFrame_pos := by norm_num only [agent12648]
  worldRadius := (2157963699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12648]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (152512011 / 100000000000 : ℝ)
  lowerTail := (898415583 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8342749943 / 1000000000000 : ℝ)
  ledger := by
    have h : (1174316697 / 1000000000000 : ℚ) +
        (9534049171 / 1000000000000000000 : ℚ) / (2157963699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (152512011 / 100000000000 : ℚ) + (898415583 / 500000000000 : ℚ) ≤
        (8342749943 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1174316697 / 1000000000000 : ℚ) +
        (9534049171 / 1000000000000000000 : ℚ) / (2157963699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (152512011 / 100000000000 : ℚ) + (898415583 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8342749943 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12648]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12648 :
    2 * 160 < 12648 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998371 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12648 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12649 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12649. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12649 : WorldParameters where
  hiddenCharge := (117427249 / 100000000000 : ℝ)
  frame := (125267123463 / 200000000000 : ℝ)
  moment := (9532079099 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12649 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (739108510267 / 500000000000 : ℝ)
    root := (1066324073 / 125000000000 : ℝ) }

noncomputable def scalar12649 : ScalarCertificate 12649 world12649 agent12649 where
  dimensionLo := 12649
  dimensionHi := 12649
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2158320199 / 1000000000000 : ℝ)
  frameLo := (125267123463 / 200000000000 : ℝ)
  frameHi := (739108510267 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12649]
  agentFrame_pos := by norm_num only [agent12649]
  worldRadius := (2158320199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12649]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (761910037 / 500000000000 : ℝ)
  lowerTail := (1795408703 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2084721011 / 250000000000 : ℝ)
  ledger := by
    have h : (117427249 / 100000000000 : ℚ) +
        (9532079099 / 1000000000000000000 : ℚ) / (2158320199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (761910037 / 500000000000 : ℚ) + (1795408703 / 1000000000000 : ℚ) ≤
        (2084721011 / 250000000000 : ℚ) := by norm_num only
    have hc : (((117427249 / 100000000000 : ℚ) +
        (9532079099 / 1000000000000000000 : ℚ) / (2158320199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (761910037 / 500000000000 : ℚ) + (1795408703 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2084721011 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12649]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12649 :
    2 * 160 < 12649 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997167 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12649 {← IO.monoMsNow}" : IO Unit)
