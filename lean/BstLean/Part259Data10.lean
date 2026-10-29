import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12275 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12275. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12275 : WorldParameters where
  hiddenCharge := (1191662583 / 1000000000000 : ℝ)
  frame := (631718262449 / 1000000000000 : ℝ)
  moment := (5155239201 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12275 : AgentParameters :=
  { agentLedgerParameters with
    charge := (374583959 / 200000000000 : ℝ)
    frame := (728993115849 / 500000000000 : ℝ)
    root := (55080409 / 6250000000 : ℝ) }

noncomputable def scalar12275 : ScalarCertificate 12275 world12275 agent12275 where
  dimensionLo := 12275
  dimensionHi := 12275
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2066182599 / 1000000000000 : ℝ)
  frameLo := (631718262449 / 1000000000000 : ℝ)
  frameHi := (728993115849 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12275]
  agentFrame_pos := by norm_num only [agent12275]
  worldRadius := (2066182599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12275]
  retainedCharge := (374583959 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (394123967 / 200000000000 : ℝ)
  lowerTail := (2253155821 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4851747029 / 500000000000 : ℝ)
  ledger := by
    have h : (1191662583 / 1000000000000 : ℚ) +
        (5155239201 / 500000000000000000 : ℚ) / (2066182599 / 1000000000000 : ℚ) ^ 2 +
        (374583959 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (394123967 / 200000000000 : ℚ) + (2253155821 / 1000000000000 : ℚ) ≤
        (4851747029 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1191662583 / 1000000000000 : ℚ) +
        (5155239201 / 500000000000000000 : ℚ) / (2066182599 / 1000000000000 : ℚ) ^ 2 +
        (374583959 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (394123967 / 200000000000 : ℚ) + (2253155821 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4851747029 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12275]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12275 :
    2 * 160 < 12275 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999997907 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12275 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12276 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12276. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12276 : WorldParameters where
  hiddenCharge := (297903423 / 250000000000 : ℝ)
  frame := (631703422371 / 1000000000000 : ℝ)
  moment := (5154140299 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12276 : AgentParameters :=
  { agentLedgerParameters with
    charge := (18721901 / 10000000000 : ℝ)
    frame := (1457945272717 / 1000000000000 : ℝ)
    root := (1762426377 / 200000000000 : ℝ) }

noncomputable def scalar12276 : ScalarCertificate 12276 world12276 agent12276 where
  dimensionLo := 12276
  dimensionHi := 12276
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2066537899 / 1000000000000 : ℝ)
  frameLo := (631703422371 / 1000000000000 : ℝ)
  frameHi := (1457945272717 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12276]
  agentFrame_pos := by norm_num only [agent12276]
  worldRadius := (2066537899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12276]
  retainedCharge := (18721901 / 10000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1968873511 / 1000000000000 : ℝ)
  lowerTail := (2251290001 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4848879147 / 500000000000 : ℝ)
  ledger := by
    have h : (297903423 / 250000000000 : ℚ) +
        (5154140299 / 500000000000000000 : ℚ) / (2066537899 / 1000000000000 : ℚ) ^ 2 +
        (18721901 / 10000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1968873511 / 1000000000000 : ℚ) + (2251290001 / 1000000000000 : ℚ) ≤
        (4848879147 / 500000000000 : ℚ) := by norm_num only
    have hc : (((297903423 / 250000000000 : ℚ) +
        (5154140299 / 500000000000000000 : ℚ) / (2066537899 / 1000000000000 : ℚ) ^ 2 +
        (18721901 / 10000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1968873511 / 1000000000000 : ℚ) + (2251290001 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4848879147 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12276]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12276 :
    2 * 160 < 12276 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999996479 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12276 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12277 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12277. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12277 : WorldParameters where
  hiddenCharge := (595782407 / 500000000000 : ℝ)
  frame := (315844292387 / 500000000000 : ℝ)
  moment := (1288260431 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12277 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1871461063 / 1000000000000 : ℝ)
    frame := (72895216719 / 50000000000 : ℝ)
    root := (55071241 / 6250000000 : ℝ) }

noncomputable def scalar12277 : ScalarCertificate 12277 world12277 agent12277 where
  dimensionLo := 12277
  dimensionHi := 12277
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2066893399 / 1000000000000 : ℝ)
  frameLo := (315844292387 / 500000000000 : ℝ)
  frameHi := (72895216719 / 50000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12277]
  agentFrame_pos := by norm_num only [agent12277]
  worldRadius := (2066893399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12277]
  retainedCharge := (1871461063 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (61472787 / 31250000000 : ℝ)
  lowerTail := (1124713107 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9692027697 / 1000000000000 : ℝ)
  ledger := by
    have h : (595782407 / 500000000000 : ℚ) +
        (1288260431 / 125000000000000000 : ℚ) / (2066893399 / 1000000000000 : ℚ) ^ 2 +
        (1871461063 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (61472787 / 31250000000 : ℚ) + (1124713107 / 500000000000 : ℚ) ≤
        (9692027697 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((595782407 / 500000000000 : ℚ) +
        (1288260431 / 125000000000000000 : ℚ) / (2066893399 / 1000000000000 : ℚ) ^ 2 +
        (1871461063 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (61472787 / 31250000000 : ℚ) + (1124713107 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9692027697 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12277]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12277 :
    2 * 160 < 12277 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2749998511 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12277 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12278 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12278. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12278 : WorldParameters where
  hiddenCharge := (23830319 / 20000000000 : ℝ)
  frame := (631673749659 / 1000000000000 : ℝ)
  moment := (10303886953 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12278 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1870732683 / 1000000000000 : ℝ)
    frame := (1457863410803 / 1000000000000 : ℝ)
    root := (1101333183 / 125000000000 : ℝ) }

noncomputable def scalar12278 : ScalarCertificate 12278 world12278 agent12278 where
  dimensionLo := 12278
  dimensionHi := 12278
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2067248699 / 1000000000000 : ℝ)
  frameLo := (631673749659 / 1000000000000 : ℝ)
  frameHi := (1457863410803 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12278]
  agentFrame_pos := by norm_num only [agent12278]
  worldRadius := (2067248699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12278]
  retainedCharge := (1870732683 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (982693183 / 500000000000 : ℝ)
  lowerTail := (1123781967 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9686302189 / 1000000000000 : ℝ)
  ledger := by
    have h : (23830319 / 20000000000 : ℚ) +
        (10303886953 / 1000000000000000000 : ℚ) / (2067248699 / 1000000000000 : ℚ) ^ 2 +
        (1870732683 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (982693183 / 500000000000 : ℚ) + (1123781967 / 500000000000 : ℚ) ≤
        (9686302189 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((23830319 / 20000000000 : ℚ) +
        (10303886953 / 1000000000000000000 : ℚ) / (2067248699 / 1000000000000 : ℚ) ^ 2 +
        (1870732683 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (982693183 / 500000000000 : ℚ) + (1123781967 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9686302189 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12278]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12278 :
    2 * 160 < 12278 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999996543 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12278 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12279 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12279. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12279 : WorldParameters where
  hiddenCharge := (1191467099 / 1000000000000 : ℝ)
  frame := (631658917023 / 1000000000000 : ℝ)
  moment := (1287711389 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12279 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1870004959 / 1000000000000 : ℝ)
    frame := (364455626963 / 250000000000 : ℝ)
    root := (4404966299 / 500000000000 : ℝ) }

noncomputable def scalar12279 : ScalarCertificate 12279 world12279 agent12279 where
  dimensionLo := 12279
  dimensionHi := 12279
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2067604099 / 1000000000000 : ℝ)
  frameLo := (631658917023 / 1000000000000 : ℝ)
  frameHi := (364455626963 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12279]
  agentFrame_pos := by norm_num only [agent12279]
  worldRadius := (2067604099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12279]
  retainedCharge := (1870004959 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1963645427 / 1000000000000 : ℝ)
  lowerTail := (1122851781 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4840290919 / 500000000000 : ℝ)
  ledger := by
    have h : (1191467099 / 1000000000000 : ℚ) +
        (1287711389 / 125000000000000000 : ℚ) / (2067604099 / 1000000000000 : ℚ) ^ 2 +
        (1870004959 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1963645427 / 1000000000000 : ℚ) + (1122851781 / 500000000000 : ℚ) ≤
        (4840290919 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1191467099 / 1000000000000 : ℚ) +
        (1287711389 / 125000000000000000 : ℚ) / (2067604099 / 1000000000000 : ℚ) ^ 2 +
        (1870004959 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1963645427 / 1000000000000 : ℚ) + (1122851781 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4840290919 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12279]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12279 :
    2 * 160 < 12279 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (549999899 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12279 {← IO.monoMsNow}" : IO Unit)
