import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12525 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12525. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12525 : WorldParameters where
  hiddenCharge := (589922529 / 500000000000 : ℝ)
  frame := (502467049 / 800000000 : ℝ)
  moment := (1956154711 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12525 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1483355193401 / 1000000000000 : ℝ)
    root := (8617819429 / 1000000000000 : ℝ) }

noncomputable def scalar12525 : ScalarCertificate 12525 world12525 agent12525 where
  dimensionLo := 12525
  dimensionHi := 12525
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2113043499 / 1000000000000 : ℝ)
  frameLo := (502467049 / 800000000 : ℝ)
  frameHi := (1483355193401 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12525]
  agentFrame_pos := by norm_num only [agent12525]
  worldRadius := (2113043499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12525]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1698454297 / 1000000000000 : ℝ)
  lowerTail := (496619701 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1770898017 / 200000000000 : ℝ)
  ledger := by
    have h : (589922529 / 500000000000 : ℚ) +
        (1956154711 / 200000000000000000 : ℚ) / (2113043499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1698454297 / 1000000000000 : ℚ) + (496619701 / 250000000000 : ℚ) ≤
        (1770898017 / 200000000000 : ℚ) := by norm_num only
    have hc : (((589922529 / 500000000000 : ℚ) +
        (1956154711 / 200000000000000000 : ℚ) / (2113043499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1698454297 / 1000000000000 : ℚ) + (496619701 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1770898017 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12525]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12525 :
    2 * 160 < 12525 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (687499679 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12525 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12526 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12526. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12526 : WorldParameters where
  hiddenCharge := (1887679 / 1600000000 : ℝ)
  frame := (62806957153 / 100000000000 : ℝ)
  moment := (2444682971 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12526 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1483320999583 / 1000000000000 : ℝ)
    root := (4308553173 / 500000000000 : ℝ) }

noncomputable def scalar12526 : ScalarCertificate 12526 world12526 agent12526 where
  dimensionLo := 12526
  dimensionHi := 12526
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2113395899 / 1000000000000 : ℝ)
  frameLo := (62806957153 / 100000000000 : ℝ)
  frameHi := (1483320999583 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12526]
  agentFrame_pos := by norm_num only [agent12526]
  worldRadius := (2113395899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12526]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1696990653 / 1000000000000 : ℝ)
  lowerTail := (1984888181 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8850202547 / 1000000000000 : ℝ)
  ledger := by
    have h : (1887679 / 1600000000 : ℚ) +
        (2444682971 / 250000000000000000 : ℚ) / (2113395899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1696990653 / 1000000000000 : ℚ) + (1984888181 / 1000000000000 : ℚ) ≤
        (8850202547 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1887679 / 1600000000 : ℚ) +
        (2444682971 / 250000000000000000 : ℚ) / (2113395899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1696990653 / 1000000000000 : ℚ) + (1984888181 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8850202547 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12526]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12526 :
    2 * 160 < 12526 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995469 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12526 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12527 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12527. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12527 : WorldParameters where
  hiddenCharge := (1179753703 / 1000000000000 : ℝ)
  frame := (628055334133 / 1000000000000 : ℝ)
  moment := (9776690809 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12527 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (741643410897 / 500000000000 : ℝ)
    root := (1723278711 / 200000000000 : ℝ) }

noncomputable def scalar12527 : ScalarCertificate 12527 world12527 agent12527 where
  dimensionLo := 12527
  dimensionHi := 12527
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2113748299 / 1000000000000 : ℝ)
  frameLo := (628055334133 / 1000000000000 : ℝ)
  frameHi := (741643410897 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12527]
  agentFrame_pos := by norm_num only [agent12527]
  worldRadius := (2113748299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12527]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (847764261 / 500000000000 : ℝ)
  lowerTail := (61978097 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4422959441 / 500000000000 : ℝ)
  ledger := by
    have h : (1179753703 / 1000000000000 : ℚ) +
        (9776690809 / 1000000000000000000 : ℚ) / (2113748299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (847764261 / 500000000000 : ℚ) + (61978097 / 31250000000 : ℚ) ≤
        (4422959441 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1179753703 / 1000000000000 : ℚ) +
        (9776690809 / 1000000000000000000 : ℚ) / (2113748299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (847764261 / 500000000000 : ℚ) + (61978097 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((4422959441 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12527]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12527 :
    2 * 160 < 12527 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999993 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12527 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12528 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12528. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12528 : WorldParameters where
  hiddenCharge := (294927011 / 250000000000 : ℝ)
  frame := (314020549529 / 500000000000 : ℝ)
  moment := (1221831291 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12528 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (296650534387 / 200000000000 : ℝ)
    root := (4307840459 / 500000000000 : ℝ) }

noncomputable def scalar12528 : ScalarCertificate 12528 world12528 agent12528 where
  dimensionLo := 12528
  dimensionHi := 12528
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2114100799 / 1000000000000 : ℝ)
  frameLo := (314020549529 / 500000000000 : ℝ)
  frameHi := (296650534387 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12528]
  agentFrame_pos := by norm_num only [agent12528]
  worldRadius := (2114100799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12528]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (423516981 / 250000000000 : ℝ)
  lowerTail := (7741061 / 3906250000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8841638947 / 1000000000000 : ℝ)
  ledger := by
    have h : (294927011 / 250000000000 : ℚ) +
        (1221831291 / 125000000000000000 : ℚ) / (2114100799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (423516981 / 250000000000 : ℚ) + (7741061 / 3906250000 : ℚ) ≤
        (8841638947 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((294927011 / 250000000000 : ℚ) +
        (1221831291 / 125000000000000000 : ℚ) / (2114100799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (423516981 / 250000000000 : ℚ) + (7741061 / 3906250000 : ℚ) : ℚ) : ℝ) ≤
        ((8841638947 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12528]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12528 :
    2 * 160 < 12528 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996209 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12528 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12529 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12529. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12529 : WorldParameters where
  hiddenCharge := (1179662397 / 1000000000000 : ℝ)
  frame := (314013433153 / 500000000000 : ℝ)
  moment := (9772610443 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12529 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1483218538081 / 1000000000000 : ℝ)
    root := (8614968503 / 1000000000000 : ℝ) }

noncomputable def scalar12529 : ScalarCertificate 12529 world12529 agent12529 where
  dimensionLo := 12529
  dimensionHi := 12529
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2114453099 / 1000000000000 : ℝ)
  frameLo := (314013433153 / 500000000000 : ℝ)
  frameHi := (1483218538081 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12529]
  agentFrame_pos := by norm_num only [agent12529]
  worldRadius := (2114453099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12529]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1692608569 / 1000000000000 : ℝ)
  lowerTail := (495031347 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1767472549 / 200000000000 : ℝ)
  ledger := by
    have h : (1179662397 / 1000000000000 : ℚ) +
        (9772610443 / 1000000000000000000 : ℚ) / (2114453099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1692608569 / 1000000000000 : ℚ) + (495031347 / 250000000000 : ℚ) ≤
        (1767472549 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1179662397 / 1000000000000 : ℚ) +
        (9772610443 / 1000000000000000000 : ℚ) / (2114453099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1692608569 / 1000000000000 : ℚ) + (495031347 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1767472549 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12529]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12529 :
    2 * 160 < 12529 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999073 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12529 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12530 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12530. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12530 : WorldParameters where
  hiddenCharge := (589808381 / 500000000000 : ℝ)
  frame := (5024101087 / 8000000000 : ℝ)
  moment := (9770571153 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12530 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (37077526183 / 25000000000 : ℝ)
    root := (861425631 / 100000000000 : ℝ) }

noncomputable def scalar12530 : ScalarCertificate 12530 world12530 agent12530 where
  dimensionLo := 12530
  dimensionHi := 12530
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2114915399 / 1000000000000 : ℝ)
  frameLo := (5024101087 / 8000000000 : ℝ)
  frameHi := (37077526183 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12530]
  agentFrame_pos := by norm_num only [agent12530]
  worldRadius := (2114915399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12530]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1690841789 / 1000000000000 : ℝ)
  lowerTail := (79125897 / 40000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8832160949 / 1000000000000 : ℝ)
  ledger := by
    have h : (589808381 / 500000000000 : ℚ) +
        (9770571153 / 1000000000000000000 : ℚ) / (2114915399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1690841789 / 1000000000000 : ℚ) + (79125897 / 40000000000 : ℚ) ≤
        (8832160949 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((589808381 / 500000000000 : ℚ) +
        (9770571153 / 1000000000000000000 : ℚ) / (2114915399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1690841789 / 1000000000000 : ℚ) + (79125897 / 40000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8832160949 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12530]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12530 :
    2 * 160 < 12530 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (274999853 / 25000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12530 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12531 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12531. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12531 : WorldParameters where
  hiddenCharge := (1179571139 / 1000000000000 : ℝ)
  frame := (125599681553 / 200000000000 : ℝ)
  moment := (9768532457 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12531 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (741533476201 / 500000000000 : ℝ)
    root := (430677217 / 50000000000 : ℝ) }

noncomputable def scalar12531 : ScalarCertificate 12531 world12531 agent12531 where
  dimensionLo := 12531
  dimensionHi := 12531
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2115267899 / 1000000000000 : ℝ)
  frameLo := (125599681553 / 200000000000 : ℝ)
  frameHi := (741533476201 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12531]
  agentFrame_pos := by norm_num only [agent12531]
  worldRadius := (2115267899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12531]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (844692879 / 500000000000 : ℝ)
  lowerTail := (39531293 / 20000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (275871653 / 31250000000 : ℝ)
  ledger := by
    have h : (1179571139 / 1000000000000 : ℚ) +
        (9768532457 / 1000000000000000000 : ℚ) / (2115267899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (844692879 / 500000000000 : ℚ) + (39531293 / 20000000000 : ℚ) ≤
        (275871653 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1179571139 / 1000000000000 : ℚ) +
        (9768532457 / 1000000000000000000 : ℚ) / (2115267899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (844692879 / 500000000000 : ℚ) + (39531293 / 20000000000 : ℚ) : ℚ) : ℝ) ≤
        ((275871653 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12531]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12531 :
    2 * 160 < 12531 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995761 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12531 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12532 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12532. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12532 : WorldParameters where
  hiddenCharge := (1179525529 / 1000000000000 : ℝ)
  frame := (25119367279 / 40000000000 : ℝ)
  moment := (1953298871 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12532 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1483032879409 / 1000000000000 : ℝ)
    root := (538302037 / 62500000000 : ℝ) }

noncomputable def scalar12532 : ScalarCertificate 12532 world12532 agent12532 where
  dimensionLo := 12532
  dimensionHi := 12532
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2115620299 / 1000000000000 : ℝ)
  frameLo := (25119367279 / 40000000000 : ℝ)
  frameHi := (1483032879409 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12532]
  agentFrame_pos := by norm_num only [agent12532]
  worldRadius := (2115620299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12532]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (843965547 / 500000000000 : ℝ)
  lowerTail := (1974983273 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2205907157 / 250000000000 : ℝ)
  ledger := by
    have h : (1179525529 / 1000000000000 : ℚ) +
        (1953298871 / 200000000000000000 : ℚ) / (2115620299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (843965547 / 500000000000 : ℚ) + (1974983273 / 1000000000000 : ℚ) ≤
        (2205907157 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1179525529 / 1000000000000 : ℚ) +
        (1953298871 / 200000000000000000 : ℚ) / (2115620299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (843965547 / 500000000000 : ℚ) + (1974983273 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2205907157 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12532]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12532 :
    2 * 160 < 12532 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999387 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12532 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12533 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12533. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12533 : WorldParameters where
  hiddenCharge := (1179479931 / 1000000000000 : ℝ)
  frame := (78496244813 / 125000000000 : ℝ)
  moment := (610278553 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12533 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (370749705593 / 250000000000 : ℝ)
    root := (4306060533 / 500000000000 : ℝ) }

noncomputable def scalar12533 : ScalarCertificate 12533 world12533 agent12533 where
  dimensionLo := 12533
  dimensionHi := 12533
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2115972799 / 1000000000000 : ℝ)
  frameLo := (78496244813 / 125000000000 : ℝ)
  frameHi := (370749705593 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12533]
  agentFrame_pos := by norm_num only [agent12533]
  worldRadius := (2115972799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12533]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1686477963 / 1000000000000 : ℝ)
  lowerTail := (1973403471 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4409684037 / 500000000000 : ℝ)
  ledger := by
    have h : (1179479931 / 1000000000000 : ℚ) +
        (610278553 / 62500000000000000 : ℚ) / (2115972799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1686477963 / 1000000000000 : ℚ) + (1973403471 / 1000000000000 : ℚ) ≤
        (4409684037 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1179479931 / 1000000000000 : ℚ) +
        (610278553 / 62500000000000000 : ℚ) / (2115972799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1686477963 / 1000000000000 : ℚ) + (1973403471 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4409684037 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12533]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12533 :
    2 * 160 < 12533 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998199 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12533 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12534 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12534. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12534 : WorldParameters where
  hiddenCharge := (235886869 / 200000000000 : ℝ)
  frame := (627955737353 / 1000000000000 : ℝ)
  moment := (4881209967 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12534 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1482964787237 / 1000000000000 : ℝ)
    root := (4305704881 / 500000000000 : ℝ) }

noncomputable def scalar12534 : ScalarCertificate 12534 world12534 agent12534 where
  dimensionLo := 12534
  dimensionHi := 12534
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2116325299 / 1000000000000 : ℝ)
  frameLo := (627955737353 / 1000000000000 : ℝ)
  frameHi := (1482964787237 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12534]
  agentFrame_pos := by norm_num only [agent12534]
  worldRadius := (2116325299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12534]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (842513147 / 500000000000 : ℝ)
  lowerTail := (1971825173 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8815111297 / 1000000000000 : ℝ)
  ledger := by
    have h : (235886869 / 200000000000 : ℚ) +
        (4881209967 / 500000000000000000 : ℚ) / (2116325299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (842513147 / 500000000000 : ℚ) + (1971825173 / 1000000000000 : ℚ) ≤
        (8815111297 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((235886869 / 200000000000 : ℚ) +
        (4881209967 / 500000000000000000 : ℚ) / (2116325299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (842513147 / 500000000000 : ℚ) + (1971825173 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8815111297 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12534]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12534 :
    2 * 160 < 12534 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999789 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12534 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12535 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12535. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12535 : WorldParameters where
  hiddenCharge := (1179388771 / 1000000000000 : ℝ)
  frame := (15698537963 / 25000000000 : ℝ)
  moment := (4880191807 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12535 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1482930773991 / 1000000000000 : ℝ)
    root := (8610698679 / 1000000000000 : ℝ) }

noncomputable def scalar12535 : ScalarCertificate 12535 world12535 agent12535 where
  dimensionLo := 12535
  dimensionHi := 12535
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2116677699 / 1000000000000 : ℝ)
  frameLo := (15698537963 / 25000000000 : ℝ)
  frameHi := (1482930773991 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12535]
  agentFrame_pos := by norm_num only [agent12535]
  worldRadius := (2116677699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12535]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (420893997 / 250000000000 : ℝ)
  lowerTail := (492562067 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (881085829 / 100000000000 : ℝ)
  ledger := by
    have h : (1179388771 / 1000000000000 : ℚ) +
        (4880191807 / 500000000000000000 : ℚ) / (2116677699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (420893997 / 250000000000 : ℚ) + (492562067 / 250000000000 : ℚ) ≤
        (881085829 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1179388771 / 1000000000000 : ℚ) +
        (4880191807 / 500000000000000000 : ℚ) / (2116677699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (420893997 / 250000000000 : ℚ) + (492562067 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((881085829 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12535]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12535 :
    2 * 160 < 12535 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999327 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12535 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12536 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12536. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12536 : WorldParameters where
  hiddenCharge := (117934321 / 100000000000 : ℝ)
  frame := (125585460401 / 200000000000 : ℝ)
  moment := (609896743 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12536 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1482896776667 / 1000000000000 : ℝ)
    root := (4304993909 / 500000000000 : ℝ) }

noncomputable def scalar12536 : ScalarCertificate 12536 world12536 agent12536 where
  dimensionLo := 12536
  dimensionHi := 12536
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2117030199 / 1000000000000 : ℝ)
  frameLo := (125585460401 / 200000000000 : ℝ)
  frameHi := (1482896776667 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12536]
  agentFrame_pos := by norm_num only [agent12536]
  worldRadius := (2117030199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12536]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1682127209 / 1000000000000 : ℝ)
  lowerTail := (1968672933 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8806608987 / 1000000000000 : ℝ)
  ledger := by
    have h : (117934321 / 100000000000 : ℚ) +
        (609896743 / 62500000000000000 : ℚ) / (2117030199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1682127209 / 1000000000000 : ℚ) + (1968672933 / 1000000000000 : ℚ) ≤
        (8806608987 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((117934321 / 100000000000 : ℚ) +
        (609896743 / 62500000000000000 : ℚ) / (2117030199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1682127209 / 1000000000000 : ℚ) + (1968672933 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8806608987 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12536]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12536 :
    2 * 160 < 12536 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999921 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12536 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12537 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12537. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12537 : WorldParameters where
  hiddenCharge := (1179297661 / 1000000000000 : ℝ)
  frame := (313956543903 / 500000000000 : ℝ)
  moment := (4878156377 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12537 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (185357850151 / 125000000000 : ℝ)
    root := (4304638589 / 500000000000 : ℝ) }

noncomputable def scalar12537 : ScalarCertificate 12537 world12537 agent12537 where
  dimensionLo := 12537
  dimensionHi := 12537
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2117382699 / 1000000000000 : ℝ)
  frameLo := (313956543903 / 500000000000 : ℝ)
  frameHi := (185357850151 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12537]
  agentFrame_pos := by norm_num only [agent12537]
  worldRadius := (2117382699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12537]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (105042493 / 62500000000 : ℝ)
  lowerTail := (245887387 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1100295431 / 125000000000 : ℝ)
  ledger := by
    have h : (1179297661 / 1000000000000 : ℚ) +
        (4878156377 / 500000000000000000 : ℚ) / (2117382699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (105042493 / 62500000000 : ℚ) + (245887387 / 125000000000 : ℚ) ≤
        (1100295431 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1179297661 / 1000000000000 : ℚ) +
        (4878156377 / 500000000000000000 : ℚ) / (2117382699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (105042493 / 62500000000 : ℚ) + (245887387 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1100295431 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12537]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12537 :
    2 * 160 < 12537 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999799 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12537 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12538 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12538. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12538 : WorldParameters where
  hiddenCharge := (294813031 / 250000000000 : ℝ)
  frame := (25115955037 / 40000000000 : ℝ)
  moment := (4877139107 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12538 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1482828847603 / 1000000000000 : ℝ)
    root := (8608566759 / 1000000000000 : ℝ) }

noncomputable def scalar12538 : ScalarCertificate 12538 world12538 agent12538 where
  dimensionLo := 12538
  dimensionHi := 12538
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2117735199 / 1000000000000 : ℝ)
  frameLo := (25115955037 / 40000000000 : ℝ)
  frameHi := (1482828847603 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12538]
  agentFrame_pos := by norm_num only [agent12538]
  worldRadius := (2117735199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12538]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (839617011 / 500000000000 : ℝ)
  lowerTail := (393105351 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8798121669 / 1000000000000 : ℝ)
  ledger := by
    have h : (294813031 / 250000000000 : ℚ) +
        (4877139107 / 500000000000000000 : ℚ) / (2117735199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (839617011 / 500000000000 : ℚ) + (393105351 / 200000000000 : ℚ) ≤
        (8798121669 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((294813031 / 250000000000 : ℚ) +
        (4877139107 / 500000000000000000 : ℚ) / (2117735199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (839617011 / 500000000000 : ℚ) + (393105351 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8798121669 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12538]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12538 :
    2 * 160 < 12538 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996161 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12538 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12539 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12539. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12539 : WorldParameters where
  hiddenCharge := (1179206599 / 1000000000000 : ℝ)
  frame := (627884666359 / 1000000000000 : ℝ)
  moment := (9752244267 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12539 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (370698727471 / 250000000000 : ℝ)
    root := (4303928281 / 500000000000 : ℝ) }

noncomputable def scalar12539 : ScalarCertificate 12539 world12539 agent12539 where
  dimensionLo := 12539
  dimensionHi := 12539
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2118087599 / 1000000000000 : ℝ)
  frameLo := (627884666359 / 1000000000000 : ℝ)
  frameHi := (370698727471 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12539]
  agentFrame_pos := by norm_num only [agent12539]
  worldRadius := (2118087599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12539]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (838894741 / 500000000000 : ℝ)
  lowerTail := (392791153 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4396941791 / 500000000000 : ℝ)
  ledger := by
    have h : (1179206599 / 1000000000000 : ℚ) +
        (9752244267 / 1000000000000000000 : ℚ) / (2118087599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (838894741 / 500000000000 : ℚ) + (392791153 / 200000000000 : ℚ) ≤
        (4396941791 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1179206599 / 1000000000000 : ℚ) +
        (9752244267 / 1000000000000000000 : ℚ) / (2118087599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (838894741 / 500000000000 : ℚ) + (392791153 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4396941791 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12539]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12539 :
    2 * 160 < 12539 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999391 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12539 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12540 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12540. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12540 : WorldParameters where
  hiddenCharge := (1179161087 / 1000000000000 : ℝ)
  frame := (627870459109 / 1000000000000 : ℝ)
  moment := (304694091 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12540 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1482677737423 / 1000000000000 : ℝ)
    root := (1721429317 / 200000000000 : ℝ) }

noncomputable def scalar12540 : ScalarCertificate 12540 world12540 agent12540 where
  dimensionLo := 12540
  dimensionHi := 12540
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2118550299 / 1000000000000 : ℝ)
  frameLo := (627870459109 / 1000000000000 : ℝ)
  frameHi := (1482677737423 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12540]
  agentFrame_pos := by norm_num only [agent12540]
  worldRadius := (2118550299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12540]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1676040559 / 1000000000000 : ℝ)
  lowerTail := (392399327 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8788727553 / 1000000000000 : ℝ)
  ledger := by
    have h : (1179161087 / 1000000000000 : ℚ) +
        (304694091 / 31250000000000000 : ℚ) / (2118550299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1676040559 / 1000000000000 : ℚ) + (392399327 / 200000000000 : ℚ) ≤
        (8788727553 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1179161087 / 1000000000000 : ℚ) +
        (304694091 / 31250000000000000 : ℚ) / (2118550299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1676040559 / 1000000000000 : ℚ) + (392399327 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8788727553 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12540]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12540 :
    2 * 160 < 12540 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995239 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12540 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12541 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12541. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12541 : WorldParameters where
  hiddenCharge := (589557793 / 500000000000 : ℝ)
  frame := (313928127087 / 500000000000 : ℝ)
  moment := (9748178149 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12541 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (296528767679 / 200000000000 : ℝ)
    root := (860643683 / 100000000000 : ℝ) }

noncomputable def scalar12541 : ScalarCertificate 12541 world12541 agent12541 where
  dimensionLo := 12541
  dimensionHi := 12541
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2118902799 / 1000000000000 : ℝ)
  frameLo := (313928127087 / 500000000000 : ℝ)
  frameHi := (296528767679 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12541]
  agentFrame_pos := by norm_num only [agent12541]
  worldRadius := (2118902799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12541]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1674599207 / 1000000000000 : ℝ)
  lowerTail := (980214477 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8784497529 / 1000000000000 : ℝ)
  ledger := by
    have h : (589557793 / 500000000000 : ℚ) +
        (9748178149 / 1000000000000000000 : ℚ) / (2118902799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1674599207 / 1000000000000 : ℚ) + (980214477 / 500000000000 : ℚ) ≤
        (8784497529 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((589557793 / 500000000000 : ℚ) +
        (9748178149 / 1000000000000000000 : ℚ) / (2118902799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1674599207 / 1000000000000 : ℚ) + (980214477 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8784497529 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12541]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12541 :
    2 * 160 < 12541 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999421 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12541 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12542 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12542. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12542 : WorldParameters where
  hiddenCharge := (589535049 / 500000000000 : ℝ)
  frame := (627842051553 / 1000000000000 : ℝ)
  moment := (9746145979 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12542 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1482609961173 / 1000000000000 : ℝ)
    root := (1721145459 / 200000000000 : ℝ) }

noncomputable def scalar12542 : ScalarCertificate 12542 world12542 agent12542 where
  dimensionLo := 12542
  dimensionHi := 12542
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2119255199 / 1000000000000 : ℝ)
  frameLo := (627842051553 / 1000000000000 : ℝ)
  frameHi := (1482609961173 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12542]
  agentFrame_pos := by norm_num only [agent12542]
  worldRadius := (2119255199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12542]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (334631841 / 200000000000 : ℝ)
  lowerTail := (30607229 / 15625000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (548766953 / 62500000000 : ℝ)
  ledger := by
    have h : (589535049 / 500000000000 : ℚ) +
        (9746145979 / 1000000000000000000 : ℚ) / (2119255199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (334631841 / 200000000000 : ℚ) + (30607229 / 15625000000 : ℚ) ≤
        (548766953 / 62500000000 : ℚ) := by norm_num only
    have hc : (((589535049 / 500000000000 : ℚ) +
        (9746145979 / 1000000000000000000 : ℚ) / (2119255199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (334631841 / 200000000000 : ℚ) + (30607229 / 15625000000 : ℚ) : ℚ) : ℝ) ≤
        ((548766953 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12542]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12542 :
    2 * 160 < 12542 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999103 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12542 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12543 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12543. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12543 : WorldParameters where
  hiddenCharge := (589512311 / 500000000000 : ℝ)
  frame := (125565570249 / 200000000000 : ℝ)
  moment := (12180143 / 1250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12543 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (148257609979 / 100000000000 : ℝ)
    root := (430250899 / 50000000000 : ℝ) }

noncomputable def scalar12543 : ScalarCertificate 12543 world12543 agent12543 where
  dimensionLo := 12543
  dimensionHi := 12543
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2119607799 / 1000000000000 : ℝ)
  frameLo := (125565570249 / 200000000000 : ℝ)
  frameHi := (148257609979 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12543]
  agentFrame_pos := by norm_num only [agent12543]
  worldRadius := (2119607799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12543]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (835860409 / 500000000000 : ℝ)
  lowerTail := (978649011 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8776048643 / 1000000000000 : ℝ)
  ledger := by
    have h : (589512311 / 500000000000 : ℚ) +
        (12180143 / 1250000000000000 : ℚ) / (2119607799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (835860409 / 500000000000 : ℚ) + (978649011 / 500000000000 : ℚ) ≤
        (8776048643 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((589512311 / 500000000000 : ℚ) +
        (12180143 / 1250000000000000 : ℚ) / (2119607799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (835860409 / 500000000000 : ℚ) + (978649011 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8776048643 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12543]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12543 :
    2 * 160 < 12543 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999907 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12543 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12544 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12544. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12544 : WorldParameters where
  hiddenCharge := (1178979159 / 1000000000000 : ℝ)
  frame := (2511254613 / 4000000000 : ℝ)
  moment := (4871041707 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12544 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (148254226019 / 100000000000 : ℝ)
    root := (1720861791 / 200000000000 : ℝ) }

noncomputable def scalar12544 : ScalarCertificate 12544 world12544 agent12544 where
  dimensionLo := 12544
  dimensionHi := 12544
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2119960399 / 1000000000000 : ℝ)
  frameLo := (2511254613 / 4000000000 : ℝ)
  frameHi := (148254226019 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12544]
  agentFrame_pos := by norm_num only [agent12544]
  worldRadius := (2119960399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12544]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1670283943 / 1000000000000 : ℝ)
  lowerTail := (977867471 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2192957477 / 250000000000 : ℝ)
  ledger := by
    have h : (1178979159 / 1000000000000 : ℚ) +
        (4871041707 / 500000000000000000 : ℚ) / (2119960399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1670283943 / 1000000000000 : ℚ) + (977867471 / 500000000000 : ℚ) ≤
        (2192957477 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1178979159 / 1000000000000 : ℚ) +
        (4871041707 / 500000000000000000 : ℚ) / (2119960399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1670283943 / 1000000000000 : ℚ) + (977867471 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2192957477 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12544]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12544 :
    2 * 160 < 12544 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999493 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12544 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12545 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12545. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12545 : WorldParameters where
  hiddenCharge := (1178933707 / 1000000000000 : ℝ)
  frame := (19618733049 / 31250000000 : ℝ)
  moment := (4870026509 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12545 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1482508442359 / 1000000000000 : ℝ)
    root := (2150900003 / 250000000000 : ℝ) }

noncomputable def scalar12545 : ScalarCertificate 12545 world12545 agent12545 where
  dimensionLo := 12545
  dimensionHi := 12545
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2120312899 / 1000000000000 : ℝ)
  frameLo := (19618733049 / 31250000000 : ℝ)
  frameHi := (1482508442359 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12545]
  agentFrame_pos := by norm_num only [agent12545]
  worldRadius := (2120312899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12545]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1668848279 / 1000000000000 : ℝ)
  lowerTail := (390834621 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4383807319 / 500000000000 : ℝ)
  ledger := by
    have h : (1178933707 / 1000000000000 : ℚ) +
        (4870026509 / 500000000000000000 : ℚ) / (2120312899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1668848279 / 1000000000000 : ℚ) + (390834621 / 200000000000 : ℚ) ≤
        (4383807319 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1178933707 / 1000000000000 : ℚ) +
        (4870026509 / 500000000000000000 : ℚ) / (2120312899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1668848279 / 1000000000000 : ℚ) + (390834621 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4383807319 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12545]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12545 :
    2 * 160 < 12545 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999419 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12545 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12546 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12546. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12546 : WorldParameters where
  hiddenCharge := (294722067 / 250000000000 : ℝ)
  frame := (313892632099 / 500000000000 : ℝ)
  moment := (4869011607 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12546 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1482474640333 / 1000000000000 : ℝ)
    root := (8602891359 / 1000000000000 : ℝ) }

noncomputable def scalar12546 : ScalarCertificate 12546 world12546 agent12546 where
  dimensionLo := 12546
  dimensionHi := 12546
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2120665499 / 1000000000000 : ℝ)
  frameLo := (313892632099 / 500000000000 : ℝ)
  frameHi := (1482474640333 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12546]
  agentFrame_pos := by norm_num only [agent12546]
  worldRadius := (2120665499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12546]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1667414193 / 1000000000000 : ℝ)
  lowerTail := (1952612889 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8763403163 / 1000000000000 : ℝ)
  ledger := by
    have h : (294722067 / 250000000000 : ℚ) +
        (4869011607 / 500000000000000000 : ℚ) / (2120665499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1667414193 / 1000000000000 : ℚ) + (1952612889 / 1000000000000 : ℚ) ≤
        (8763403163 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((294722067 / 250000000000 : ℚ) +
        (4869011607 / 500000000000000000 : ℚ) / (2120665499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1667414193 / 1000000000000 : ℚ) + (1952612889 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8763403163 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12546]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12546 :
    2 * 160 < 12546 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999083 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12546 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12547 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12547. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12547 : WorldParameters where
  hiddenCharge := (1178842841 / 1000000000000 : ℝ)
  frame := (313885536569 / 500000000000 : ℝ)
  moment := (9735994001 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12547 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (741220430027 / 500000000000 : ℝ)
    root := (344087317 / 40000000000 : ℝ) }

noncomputable def scalar12547 : ScalarCertificate 12547 world12547 agent12547 where
  dimensionLo := 12547
  dimensionHi := 12547
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2121017999 / 1000000000000 : ℝ)
  frameLo := (313885536569 / 500000000000 : ℝ)
  frameHi := (741220430027 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12547]
  agentFrame_pos := by norm_num only [agent12547]
  worldRadius := (2121017999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12547]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1665981449 / 1000000000000 : ℝ)
  lowerTail := (1951054047 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8759195413 / 1000000000000 : ℝ)
  ledger := by
    have h : (1178842841 / 1000000000000 : ℚ) +
        (9735994001 / 1000000000000000000 : ℚ) / (2121017999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1665981449 / 1000000000000 : ℚ) + (1951054047 / 1000000000000 : ℚ) ≤
        (8759195413 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1178842841 / 1000000000000 : ℚ) +
        (9735994001 / 1000000000000000000 : ℚ) / (2121017999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1665981449 / 1000000000000 : ℚ) + (1951054047 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8759195413 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12547]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12547 :
    2 * 160 < 12547 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998277 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12547 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12548 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12548. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12548 : WorldParameters where
  hiddenCharge := (589398713 / 500000000000 : ℝ)
  frame := (62775688439 / 100000000000 : ℝ)
  moment := (9733965379 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12548 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (296481408397 / 200000000000 : ℝ)
    root := (8601474711 / 1000000000000 : ℝ) }

noncomputable def scalar12548 : ScalarCertificate 12548 world12548 agent12548 where
  dimensionLo := 12548
  dimensionHi := 12548
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2121370699 / 1000000000000 : ℝ)
  frameLo := (62775688439 / 100000000000 : ℝ)
  frameHi := (296481408397 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12548]
  agentFrame_pos := by norm_num only [agent12548]
  worldRadius := (2121370699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12548]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (332910009 / 200000000000 : ℝ)
  lowerTail := (1949496537 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8754990727 / 1000000000000 : ℝ)
  ledger := by
    have h : (589398713 / 500000000000 : ℚ) +
        (9733965379 / 1000000000000000000 : ℚ) / (2121370699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (332910009 / 200000000000 : ℚ) + (1949496537 / 1000000000000 : ℚ) ≤
        (8754990727 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((589398713 / 500000000000 : ℚ) +
        (9733965379 / 1000000000000000000 : ℚ) / (2121370699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (332910009 / 200000000000 : ℚ) + (1949496537 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8754990727 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12548]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12548 :
    2 * 160 < 12548 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (343749813 / 31250000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12548 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12549 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12549. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12549 : WorldParameters where
  hiddenCharge := (1178752023 / 1000000000000 : ℝ)
  frame := (627742697951 / 1000000000000 : ℝ)
  moment := (9731937347 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12549 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (148237296589 / 100000000000 : ℝ)
    root := (8600766717 / 1000000000000 : ℝ) }

noncomputable def scalar12549 : ScalarCertificate 12549 world12549 agent12549 where
  dimensionLo := 12549
  dimensionHi := 12549
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2121723599 / 1000000000000 : ℝ)
  frameLo := (627742697951 / 1000000000000 : ℝ)
  frameHi := (148237296589 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12549]
  agentFrame_pos := by norm_num only [agent12549]
  worldRadius := (2121723599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12549]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1663118891 / 1000000000000 : ℝ)
  lowerTail := (973969511 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8750786681 / 1000000000000 : ℝ)
  ledger := by
    have h : (1178752023 / 1000000000000 : ℚ) +
        (9731937347 / 1000000000000000000 : ℚ) / (2121723599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1663118891 / 1000000000000 : ℚ) + (973969511 / 500000000000 : ℚ) ≤
        (8750786681 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1178752023 / 1000000000000 : ℚ) +
        (9731937347 / 1000000000000000000 : ℚ) / (2121723599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1663118891 / 1000000000000 : ℚ) + (973969511 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8750786681 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12549]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12549 :
    2 * 160 < 12549 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994749 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12549 {← IO.monoMsNow}" : IO Unit)
