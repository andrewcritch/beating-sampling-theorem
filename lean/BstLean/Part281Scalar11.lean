import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 12134 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12134. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12134 : WorldParameters where
  hiddenCharge := (1198692749 / 1000000000000 : ℝ)
  frame := (9903685537 / 15625000000 : ℝ)
  moment := (10627042481 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12134 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (300232779233 / 200000000000 : ℝ)
    root := (7508799991 / 1000000000000 : ℝ) }

noncomputable def scalar12134 : ScalarCertificate 12134 world12134 agent12134 where
  dimensionLo := 12134
  dimensionHi := 12134
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2323036999 / 1000000000000 : ℝ)
  frameLo := (9903685537 / 15625000000 : ℝ)
  frameHi := (300232779233 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12134]
  agentFrame_pos := by norm_num only [agent12134]
  worldRadius := (2323036999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12134]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (667095791 / 500000000000 : ℝ)
  lowerTail := (845263501 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (249743881 / 31250000000 : ℝ)
  ledger := by
    have h : (1198692749 / 1000000000000 : ℚ) +
        (10627042481 / 1000000000000000000 : ℚ) / (2323036999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (667095791 / 500000000000 : ℚ) + (845263501 / 500000000000 : ℚ) ≤
        (249743881 / 31250000000 : ℚ) := by norm_num only
    have hc : (((1198692749 / 1000000000000 : ℚ) +
        (10627042481 / 1000000000000000000 : ℚ) / (2323036999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (667095791 / 500000000000 : ℚ) + (845263501 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((249743881 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12134]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12134 :
    2 * 160 < 12134 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998907 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12134 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12135 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12135. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12135 : WorldParameters where
  hiddenCharge := (1198641919 / 1000000000000 : ℝ)
  frame := (158455169419 / 250000000000 : ℝ)
  moment := (1062474983 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12135 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1501114881499 / 1000000000000 : ℝ)
    root := (7508124911 / 1000000000000 : ℝ) }

noncomputable def scalar12135 : ScalarCertificate 12135 world12135 agent12135 where
  dimensionLo := 12135
  dimensionHi := 12135
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2323439999 / 1000000000000 : ℝ)
  frameLo := (158455169419 / 250000000000 : ℝ)
  frameHi := (1501114881499 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12135]
  agentFrame_pos := by norm_num only [agent12135]
  worldRadius := (2323439999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12135]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1332993519 / 1000000000000 : ℝ)
  lowerTail := (1689119833 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3994020183 / 500000000000 : ℝ)
  ledger := by
    have h : (1198641919 / 1000000000000 : ℚ) +
        (1062474983 / 100000000000000000 : ℚ) / (2323439999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1332993519 / 1000000000000 : ℚ) + (1689119833 / 1000000000000 : ℚ) ≤
        (3994020183 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1198641919 / 1000000000000 : ℚ) +
        (1062474983 / 100000000000000000 : ℚ) / (2323439999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1332993519 / 1000000000000 : ℚ) + (1689119833 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3994020183 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12135]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12135 :
    2 * 160 < 12135 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (274999883 / 25000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12135 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12136 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12136. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12136 : WorldParameters where
  hiddenCharge := (599295551 / 500000000000 : ℝ)
  frame := (316902741781 / 500000000000 : ℝ)
  moment := (1062245787 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12136 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (750532945037 / 500000000000 : ℝ)
    root := (7507450123 / 1000000000000 : ℝ) }

noncomputable def scalar12136 : ScalarCertificate 12136 world12136 agent12136 where
  dimensionLo := 12136
  dimensionHi := 12136
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2323842799 / 1000000000000 : ℝ)
  frameLo := (316902741781 / 500000000000 : ℝ)
  frameHi := (750532945037 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12136]
  agentFrame_pos := by norm_num only [agent12136]
  worldRadius := (2323842799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12136]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1331796599 / 1000000000000 : ℝ)
  lowerTail := (843856957 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3992140031 / 500000000000 : ℝ)
  ledger := by
    have h : (599295551 / 500000000000 : ℚ) +
        (1062245787 / 100000000000000000 : ℚ) / (2323842799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1331796599 / 1000000000000 : ℚ) + (843856957 / 500000000000 : ℚ) ≤
        (3992140031 / 500000000000 : ℚ) := by norm_num only
    have hc : (((599295551 / 500000000000 : ℚ) +
        (1062245787 / 100000000000000000 : ℚ) / (2323842799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1331796599 / 1000000000000 : ℚ) + (843856957 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3992140031 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12136]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12136 :
    2 * 160 < 12136 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996153 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12136 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12137 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12137. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12137 : WorldParameters where
  hiddenCharge := (11985403 / 10000000000 : ℝ)
  frame := (79223786503 / 125000000000 : ℝ)
  moment := (53100833 / 5000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12137 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1501016927931 / 1000000000000 : ℝ)
    root := (7506775551 / 1000000000000 : ℝ) }

noncomputable def scalar12137 : ScalarCertificate 12137 world12137 agent12137 where
  dimensionLo := 12137
  dimensionHi := 12137
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2324245699 / 1000000000000 : ℝ)
  frameLo := (79223786503 / 125000000000 : ℝ)
  frameHi := (1501016927931 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12137]
  agentFrame_pos := by norm_num only [agent12137]
  worldRadius := (2324245699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12137]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1330601019 / 1000000000000 : ℝ)
  lowerTail := (843154743 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1995130803 / 250000000000 : ℝ)
  ledger := by
    have h : (11985403 / 10000000000 : ℚ) +
        (53100833 / 5000000000000000 : ℚ) / (2324245699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1330601019 / 1000000000000 : ℚ) + (843154743 / 500000000000 : ℚ) ≤
        (1995130803 / 250000000000 : ℚ) := by norm_num only
    have hc : (((11985403 / 10000000000 : ℚ) +
        (53100833 / 5000000000000000 : ℚ) / (2324245699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1330601019 / 1000000000000 : ℚ) + (843154743 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1995130803 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12137]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12137 :
    2 * 160 < 12137 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995403 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12137 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12138 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12138. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12138 : WorldParameters where
  hiddenCharge := (149811189 / 125000000000 : ℝ)
  frame := (633775103061 / 1000000000000 : ℝ)
  moment := (5308938011 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12138 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1500967988991 / 1000000000000 : ℝ)
    root := (7506101193 / 1000000000000 : ℝ) }

noncomputable def scalar12138 : ScalarCertificate 12138 world12138 agent12138 where
  dimensionLo := 12138
  dimensionHi := 12138
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2324648699 / 1000000000000 : ℝ)
  frameLo := (633775103061 / 1000000000000 : ℝ)
  frameHi := (1500967988991 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12138]
  agentFrame_pos := by norm_num only [agent12138]
  worldRadius := (2324648699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12138]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (664703377 / 500000000000 : ℝ)
  lowerTail := (842453257 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3988384877 / 500000000000 : ℝ)
  ledger := by
    have h : (149811189 / 125000000000 : ℚ) +
        (5308938011 / 500000000000000000 : ℚ) / (2324648699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (664703377 / 500000000000 : ℚ) + (842453257 / 500000000000 : ℚ) ≤
        (3988384877 / 500000000000 : ℚ) := by norm_num only
    have hc : (((149811189 / 125000000000 : ℚ) +
        (5308938011 / 500000000000000000 : ℚ) / (2324648699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (664703377 / 500000000000 : ℚ) + (842453257 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3988384877 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12138]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12138 :
    2 * 160 < 12138 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (687499939 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12138 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12139 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12139. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12139 : WorldParameters where
  hiddenCharge := (599219369 / 500000000000 : ℝ)
  frame := (316879958337 / 500000000000 : ℝ)
  moment := (10615586133 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12139 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1500919085351 / 1000000000000 : ℝ)
    root := (3752713487 / 500000000000 : ℝ) }

noncomputable def scalar12139 : ScalarCertificate 12139 world12139 agent12139 where
  dimensionLo := 12139
  dimensionHi := 12139
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2325051599 / 1000000000000 : ℝ)
  frameLo := (316879958337 / 500000000000 : ℝ)
  frameHi := (1500919085351 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12139]
  agentFrame_pos := by norm_num only [agent12139]
  worldRadius := (2325051599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12139]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (265642727 / 200000000000 : ℝ)
  lowerTail := (1683504817 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1993254919 / 250000000000 : ℝ)
  ledger := by
    have h : (599219369 / 500000000000 : ℚ) +
        (10615586133 / 1000000000000000000 : ℚ) / (2325051599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (265642727 / 200000000000 : ℚ) + (1683504817 / 1000000000000 : ℚ) ≤
        (1993254919 / 250000000000 : ℚ) := by norm_num only
    have hc : (((599219369 / 500000000000 : ℚ) +
        (10615586133 / 1000000000000000000 : ℚ) / (2325051599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (265642727 / 200000000000 : ℚ) + (1683504817 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1993254919 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12139]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12139 :
    2 * 160 < 12139 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997511 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12139 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12140 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12140. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12140 : WorldParameters where
  hiddenCharge := (599193989 / 500000000000 : ℝ)
  frame := (633744732861 / 1000000000000 : ℝ)
  moment := (5306648467 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12140 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (750435008541 / 500000000000 : ℝ)
    root := (3752376523 / 500000000000 : ℝ) }

noncomputable def scalar12140 : ScalarCertificate 12140 world12140 agent12140 where
  dimensionLo := 12140
  dimensionHi := 12140
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2325454899 / 1000000000000 : ℝ)
  frameLo := (633744732861 / 1000000000000 : ℝ)
  frameHi := (750435008541 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12140]
  agentFrame_pos := by norm_num only [agent12140]
  worldRadius := (2325454899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12140]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (663510681 / 500000000000 : ℝ)
  lowerTail := (841051957 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7969271351 / 1000000000000 : ℝ)
  ledger := by
    have h : (599193989 / 500000000000 : ℚ) +
        (5306648467 / 500000000000000000 : ℚ) / (2325454899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (663510681 / 500000000000 : ℚ) + (841051957 / 500000000000 : ℚ) ≤
        (7969271351 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((599193989 / 500000000000 : ℚ) +
        (5306648467 / 500000000000000000 : ℚ) / (2325454899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (663510681 / 500000000000 : ℚ) + (841051957 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7969271351 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12140]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12140 :
    2 * 160 < 12140 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998437 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12140 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12141 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12141. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12141 : WorldParameters where
  hiddenCharge := (74896077 / 62500000000 : ℝ)
  frame := (633729551621 / 1000000000000 : ℝ)
  moment := (424440337 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12141 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1500820814479 / 1000000000000 : ℝ)
    root := (7504079333 / 1000000000000 : ℝ) }

noncomputable def scalar12141 : ScalarCertificate 12141 world12141 agent12141 where
  dimensionLo := 12141
  dimensionHi := 12141
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2325858299 / 1000000000000 : ℝ)
  frameLo := (633729551621 / 1000000000000 : ℝ)
  frameHi := (1500820814479 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12141]
  agentFrame_pos := by norm_num only [agent12141]
  worldRadius := (2325858299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12141]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (265165953 / 200000000000 : ℝ)
  lowerTail := (420175907 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (398276247 / 50000000000 : ℝ)
  ledger := by
    have h : (74896077 / 62500000000 : ℚ) +
        (424440337 / 40000000000000000 : ℚ) / (2325858299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (265165953 / 200000000000 : ℚ) + (420175907 / 250000000000 : ℚ) ≤
        (398276247 / 50000000000 : ℚ) := by norm_num only
    have hc : (((74896077 / 62500000000 : ℚ) +
        (424440337 / 40000000000000000 : ℚ) / (2325858299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (265165953 / 200000000000 : ℚ) + (420175907 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((398276247 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12141]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12141 :
    2 * 160 < 12141 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999531 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12141 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12142 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12142. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12142 : WorldParameters where
  hiddenCharge := (2396573 / 2000000000 : ℝ)
  frame := (126742874591 / 200000000000 : ℝ)
  moment := (2121744121 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12142 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (750385823573 / 500000000000 : ℝ)
    root := (3751702879 / 500000000000 : ℝ) }

noncomputable def scalar12142 : ScalarCertificate 12142 world12142 agent12142 where
  dimensionLo := 12142
  dimensionHi := 12142
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2326261799 / 1000000000000 : ℝ)
  frameLo := (126742874591 / 200000000000 : ℝ)
  frameHi := (750385823573 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12142]
  agentFrame_pos := by norm_num only [agent12142]
  worldRadius := (2326261799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12142]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1324639467 / 1000000000000 : ℝ)
  lowerTail := (419826199 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (497611369 / 62500000000 : ℝ)
  ledger := by
    have h : (2396573 / 2000000000 : ℚ) +
        (2121744121 / 200000000000000000 : ℚ) / (2326261799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1324639467 / 1000000000000 : ℚ) + (419826199 / 250000000000 : ℚ) ≤
        (497611369 / 62500000000 : ℚ) := by norm_num only
    have hc : (((2396573 / 2000000000 : ℚ) +
        (2121744121 / 200000000000000000 : ℚ) / (2326261799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1324639467 / 1000000000000 : ℚ) + (419826199 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((497611369 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12142]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12142 :
    2 * 160 < 12142 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994117 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12142 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12143 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12143. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12143 : WorldParameters where
  hiddenCharge := (1198235783 / 1000000000000 : ℝ)
  frame := (633699196861 / 1000000000000 : ℝ)
  moment := (424257339 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12143 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (375180624223 / 250000000000 : ℝ)
    root := (3751366237 / 500000000000 : ℝ) }

noncomputable def scalar12143 : ScalarCertificate 12143 world12143 agent12143 where
  dimensionLo := 12143
  dimensionHi := 12143
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2326665099 / 1000000000000 : ℝ)
  frameLo := (633699196861 / 1000000000000 : ℝ)
  frameHi := (375180624223 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12143]
  agentFrame_pos := by norm_num only [agent12143]
  worldRadius := (2326665099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12143]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (661725139 / 500000000000 : ℝ)
  lowerTail := (1677907173 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (795804231 / 100000000000 : ℝ)
  ledger := by
    have h : (1198235783 / 1000000000000 : ℚ) +
        (424257339 / 40000000000000000 : ℚ) / (2326665099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (661725139 / 500000000000 : ℚ) + (1677907173 / 1000000000000 : ℚ) ≤
        (795804231 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1198235783 / 1000000000000 : ℚ) +
        (424257339 / 40000000000000000 : ℚ) / (2326665099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (661725139 / 500000000000 : ℚ) + (1677907173 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((795804231 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12143]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12143 :
    2 * 160 < 12143 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999921 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12143 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12144 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12144. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12144 : WorldParameters where
  hiddenCharge := (1198185079 / 1000000000000 : ℝ)
  frame := (316842011669 / 500000000000 : ℝ)
  moment := (10604147033 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12144 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (150067338187 / 100000000000 : ℝ)
    root := (1875514851 / 250000000000 : ℝ) }

noncomputable def scalar12144 : ScalarCertificate 12144 world12144 agent12144 where
  dimensionLo := 12144
  dimensionHi := 12144
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2327068599 / 1000000000000 : ℝ)
  frameLo := (316842011669 / 500000000000 : ℝ)
  frameHi := (150067338187 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12144]
  agentFrame_pos := by norm_num only [agent12144]
  worldRadius := (2327068599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12144]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (661131261 / 500000000000 : ℝ)
  lowerTail := (1676511153 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1988576551 / 250000000000 : ℝ)
  ledger := by
    have h : (1198185079 / 1000000000000 : ℚ) +
        (10604147033 / 1000000000000000000 : ℚ) / (2327068599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (661131261 / 500000000000 : ℚ) + (1676511153 / 1000000000000 : ℚ) ≤
        (1988576551 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1198185079 / 1000000000000 : ℚ) +
        (10604147033 / 1000000000000000000 : ℚ) / (2327068599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (661131261 / 500000000000 : ℚ) + (1676511153 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1988576551 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12144]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12144 :
    2 * 160 < 12144 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999831 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12144 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12145 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12145. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12145 : WorldParameters where
  hiddenCharge := (119813439 / 100000000000 : ℝ)
  frame := (316834426193 / 500000000000 : ℝ)
  moment := (66261633 / 6250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12145 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1500624296001 / 1000000000000 : ℝ)
    root := (7501386549 / 1000000000000 : ℝ) }

noncomputable def scalar12145 : ScalarCertificate 12145 world12145 agent12145 where
  dimensionLo := 12145
  dimensionHi := 12145
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2327471899 / 1000000000000 : ℝ)
  frameLo := (316834426193 / 500000000000 : ℝ)
  frameHi := (1500624296001 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12145]
  agentFrame_pos := by norm_num only [agent12145]
  worldRadius := (2327471899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12145]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1321075863 / 1000000000000 : ℝ)
  lowerTail := (1675116341 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (318022941 / 40000000000 : ℝ)
  ledger := by
    have h : (119813439 / 100000000000 : ℚ) +
        (66261633 / 6250000000000000 : ℚ) / (2327471899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1321075863 / 1000000000000 : ℚ) + (1675116341 / 1000000000000 : ℚ) ≤
        (318022941 / 40000000000 : ℚ) := by norm_num only
    have hc : (((119813439 / 100000000000 : ℚ) +
        (66261633 / 6250000000000000 : ℚ) / (2327471899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1321075863 / 1000000000000 : ℚ) + (1675116341 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((318022941 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12145]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12145 :
    2 * 160 < 12145 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997709 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12145 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12146 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12146. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12146 : WorldParameters where
  hiddenCharge := (599041857 / 500000000000 : ℝ)
  frame := (126730736801 / 200000000000 : ℝ)
  moment := (2119915243 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12146 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (300115047853 / 200000000000 : ℝ)
    root := (750071383 / 100000000000 : ℝ) }

noncomputable def scalar12146 : ScalarCertificate 12146 world12146 agent12146 where
  dimensionLo := 12146
  dimensionHi := 12146
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2327875499 / 1000000000000 : ℝ)
  frameLo := (126730736801 / 200000000000 : ℝ)
  frameHi := (300115047853 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12146]
  agentFrame_pos := by norm_num only [agent12146]
  worldRadius := (2327875499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12146]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (329972657 / 250000000000 : ℝ)
  lowerTail := (2677957 / 1600000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7946844149 / 1000000000000 : ℝ)
  ledger := by
    have h : (599041857 / 500000000000 : ℚ) +
        (2119915243 / 200000000000000000 : ℚ) / (2327875499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (329972657 / 250000000000 : ℚ) + (2677957 / 1600000000 : ℚ) ≤
        (7946844149 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((599041857 / 500000000000 : ℚ) +
        (2119915243 / 200000000000000000 : ℚ) / (2327875499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (329972657 / 250000000000 : ℚ) + (2677957 / 1600000000 : ℚ) : ℚ) : ℝ) ≤
        ((7946844149 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12146]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12146 :
    2 * 160 < 12146 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995551 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12146 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12147 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12147. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12147 : WorldParameters where
  hiddenCharge := (1198033053 / 1000000000000 : ℝ)
  frame := (39602407387 / 62500000000 : ℝ)
  moment := (5298645919 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12147 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (375131551397 / 250000000000 : ℝ)
    root := (3750020701 / 500000000000 : ℝ) }

noncomputable def scalar12147 : ScalarCertificate 12147 world12147 agent12147 where
  dimensionLo := 12147
  dimensionHi := 12147
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2328278899 / 1000000000000 : ℝ)
  frameLo := (39602407387 / 62500000000 : ℝ)
  frameHi := (375131551397 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12147]
  agentFrame_pos := by norm_num only [agent12147]
  worldRadius := (2328278899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12147]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1318706521 / 1000000000000 : ℝ)
  lowerTail := (1672331143 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (496444891 / 62500000000 : ℝ)
  ledger := by
    have h : (1198033053 / 1000000000000 : ℚ) +
        (5298645919 / 500000000000000000 : ℚ) / (2328278899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1318706521 / 1000000000000 : ℚ) + (1672331143 / 1000000000000 : ℚ) ≤
        (496444891 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1198033053 / 1000000000000 : ℚ) +
        (5298645919 / 500000000000000000 : ℚ) / (2328278899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1318706521 / 1000000000000 : ℚ) + (1672331143 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((496444891 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12147]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12147 :
    2 * 160 < 12147 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998581 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12147 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12148 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12148. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12148 : WorldParameters where
  hiddenCharge := (239596481 / 200000000000 : ℝ)
  frame := (633623354949 / 1000000000000 : ℝ)
  moment := (10595008149 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12148 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (75023860353 / 50000000000 : ℝ)
    root := (1874842297 / 250000000000 : ℝ) }

noncomputable def scalar12148 : ScalarCertificate 12148 world12148 agent12148 where
  dimensionLo := 12148
  dimensionHi := 12148
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2328682199 / 1000000000000 : ℝ)
  frameLo := (633623354949 / 1000000000000 : ℝ)
  frameHi := (75023860353 / 50000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12148]
  agentFrame_pos := by norm_num only [agent12148]
  worldRadius := (2328682199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12148]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1317523607 / 1000000000000 : ℝ)
  lowerTail := (1670940487 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7939395837 / 1000000000000 : ℝ)
  ledger := by
    have h : (239596481 / 200000000000 : ℚ) +
        (10595008149 / 1000000000000000000 : ℚ) / (2328682199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1317523607 / 1000000000000 : ℚ) + (1670940487 / 1000000000000 : ℚ) ≤
        (7939395837 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((239596481 / 200000000000 : ℚ) +
        (10595008149 / 1000000000000000000 : ℚ) / (2328682199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1317523607 / 1000000000000 : ℚ) + (1670940487 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7939395837 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12148]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12148 :
    2 * 160 < 12148 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994911 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12148 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12149 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12149. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12149 : WorldParameters where
  hiddenCharge := (299482943 / 250000000000 : ℝ)
  frame := (316804097137 / 500000000000 : ℝ)
  moment := (10592725147 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12149 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1500428231551 / 1000000000000 : ℝ)
    root := (7498697111 / 1000000000000 : ℝ) }

noncomputable def scalar12149 : ScalarCertificate 12149 world12149 agent12149 where
  dimensionLo := 12149
  dimensionHi := 12149
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2329085799 / 1000000000000 : ℝ)
  frameLo := (316804097137 / 500000000000 : ℝ)
  frameHi := (1500428231551 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12149]
  agentFrame_pos := by norm_num only [agent12149]
  worldRadius := (2329085799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12149]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1316342089 / 1000000000000 : ℝ)
  lowerTail := (166955139 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1983919163 / 250000000000 : ℝ)
  ledger := by
    have h : (299482943 / 250000000000 : ℚ) +
        (10592725147 / 1000000000000000000 : ℚ) / (2329085799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1316342089 / 1000000000000 : ℚ) + (166955139 / 100000000000 : ℚ) ≤
        (1983919163 / 250000000000 : ℚ) := by norm_num only
    have hc : (((299482943 / 250000000000 : ℚ) +
        (10592725147 / 1000000000000000000 : ℚ) / (2329085799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1316342089 / 1000000000000 : ℚ) + (166955139 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1983919163 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12149]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12149 :
    2 * 160 < 12149 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996373 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12149 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12150 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12150. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12150 : WorldParameters where
  hiddenCharge := (18716893 / 15625000000 : ℝ)
  frame := (316796518083 / 500000000000 : ℝ)
  moment := (10590442833 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12150 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (187547410637 / 125000000000 : ℝ)
    root := (1874506331 / 250000000000 : ℝ) }

noncomputable def scalar12150 : ScalarCertificate 12150 world12150 agent12150 where
  dimensionLo := 12150
  dimensionHi := 12150
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2329489199 / 1000000000000 : ℝ)
  frameLo := (316796518083 / 500000000000 : ℝ)
  frameHi := (187547410637 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12150]
  agentFrame_pos := by norm_num only [agent12150]
  worldRadius := (2329489199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12150]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1315161719 / 1000000000000 : ℝ)
  lowerTail := (333632711 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1982990249 / 250000000000 : ℝ)
  ledger := by
    have h : (18716893 / 15625000000 : ℚ) +
        (10590442833 / 1000000000000000000 : ℚ) / (2329489199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1315161719 / 1000000000000 : ℚ) + (333632711 / 200000000000 : ℚ) ≤
        (1982990249 / 250000000000 : ℚ) := by norm_num only
    have hc : (((18716893 / 15625000000 : ℚ) +
        (10590442833 / 1000000000000000000 : ℚ) / (2329489199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1315161719 / 1000000000000 : ℚ) + (333632711 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1982990249 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12150]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12150 :
    2 * 160 < 12150 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997007 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12150 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12151 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12151. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12151 : WorldParameters where
  hiddenCharge := (1197830547 / 1000000000000 : ℝ)
  frame := (1013724609 / 1600000000 : ℝ)
  moment := (5294080603 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12151 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (375082591919 / 250000000000 : ℝ)
    root := (5997883 / 800000000 : ℝ) }

noncomputable def scalar12151 : ScalarCertificate 12151 world12151 agent12151 where
  dimensionLo := 12151
  dimensionHi := 12151
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2329892599 / 1000000000000 : ℝ)
  frameLo := (1013724609 / 1600000000 : ℝ)
  frameHi := (375082591919 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12151]
  agentFrame_pos := by norm_num only [agent12151]
  worldRadius := (2329892599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12151]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1313982591 / 1000000000000 : ℝ)
  lowerTail := (1666777099 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3964124373 / 500000000000 : ℝ)
  ledger := by
    have h : (1197830547 / 1000000000000 : ℚ) +
        (5294080603 / 500000000000000000 : ℚ) / (2329892599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1313982591 / 1000000000000 : ℚ) + (1666777099 / 1000000000000 : ℚ) ≤
        (3964124373 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1197830547 / 1000000000000 : ℚ) +
        (5294080603 / 500000000000000000 : ℚ) / (2329892599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1313982591 / 1000000000000 : ℚ) + (1666777099 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3964124373 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12151]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12151 :
    2 * 160 < 12151 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996783 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12151 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12152 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12152. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12152 : WorldParameters where
  hiddenCharge := (299444989 / 250000000000 : ℝ)
  frame := (633562727649 / 1000000000000 : ℝ)
  moment := (2117176053 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12152 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1500281479271 / 1000000000000 : ℝ)
    root := (937085289 / 125000000000 : ℝ) }

noncomputable def scalar12152 : ScalarCertificate 12152 world12152 agent12152 where
  dimensionLo := 12152
  dimensionHi := 12152
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2330295999 / 1000000000000 : ℝ)
  frameLo := (633562727649 / 1000000000000 : ℝ)
  frameHi := (1500281479271 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12152]
  agentFrame_pos := by norm_num only [agent12152]
  worldRadius := (2330295999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12152]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (656402323 / 500000000000 : ℝ)
  lowerTail := (832695979 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (316981591 / 40000000000 : ℝ)
  ledger := by
    have h : (299444989 / 250000000000 : ℚ) +
        (2117176053 / 200000000000000000 : ℚ) / (2330295999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (656402323 / 500000000000 : ℚ) + (832695979 / 500000000000 : ℚ) ≤
        (316981591 / 40000000000 : ℚ) := by norm_num only
    have hc : (((299444989 / 250000000000 : ℚ) +
        (2117176053 / 200000000000000000 : ℚ) / (2330295999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (656402323 / 500000000000 : ℚ) + (832695979 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((316981591 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12152]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12152 :
    2 * 160 < 12152 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995671 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12152 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12153 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12153. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12153 : WorldParameters where
  hiddenCharge := (598864689 / 500000000000 : ℝ)
  frame := (15838689431 / 25000000000 : ℝ)
  moment := (10583600011 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12153 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (750116306903 / 500000000000 : ℝ)
    root := (1874002791 / 250000000000 : ℝ) }

noncomputable def scalar12153 : ScalarCertificate 12153 world12153 agent12153 where
  dimensionLo := 12153
  dimensionHi := 12153
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2330699499 / 1000000000000 : ℝ)
  frameLo := (15838689431 / 25000000000 : ℝ)
  frameHi := (750116306903 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12153]
  agentFrame_pos := by norm_num only [agent12153]
  worldRadius := (2330699499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12153]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1311628051 / 1000000000000 : ℝ)
  lowerTail := (1664008313 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3960417133 / 500000000000 : ℝ)
  ledger := by
    have h : (598864689 / 500000000000 : ℚ) +
        (10583600011 / 1000000000000000000 : ℚ) / (2330699499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1311628051 / 1000000000000 : ℚ) + (1664008313 / 1000000000000 : ℚ) ≤
        (3960417133 / 500000000000 : ℚ) := by norm_num only
    have hc : (((598864689 / 500000000000 : ℚ) +
        (10583600011 / 1000000000000000000 : ℚ) / (2330699499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1311628051 / 1000000000000 : ℚ) + (1664008313 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3960417133 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12153]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12153 :
    2 * 160 < 12153 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999791 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12153 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12154 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12154. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12154 : WorldParameters where
  hiddenCharge := (239535763 / 200000000000 : ℝ)
  frame := (316766214697 / 500000000000 : ℝ)
  moment := (10581320443 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12154 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1500183783371 / 1000000000000 : ℝ)
    root := (7495340229 / 1000000000000 : ℝ) }

noncomputable def scalar12154 : ScalarCertificate 12154 world12154 agent12154 where
  dimensionLo := 12154
  dimensionHi := 12154
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2331102999 / 1000000000000 : ℝ)
  frameLo := (316766214697 / 500000000000 : ℝ)
  frameHi := (1500183783371 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12154]
  agentFrame_pos := by norm_num only [agent12154]
  worldRadius := (2331102999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12154]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1310452719 / 1000000000000 : ℝ)
  lowerTail := (66505043 / 40000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1583426441 / 200000000000 : ℝ)
  ledger := by
    have h : (239535763 / 200000000000 : ℚ) +
        (10581320443 / 1000000000000000000 : ℚ) / (2331102999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1310452719 / 1000000000000 : ℚ) + (66505043 / 40000000000 : ℚ) ≤
        (1583426441 / 200000000000 : ℚ) := by norm_num only
    have hc : (((239535763 / 200000000000 : ℚ) +
        (10581320443 / 1000000000000000000 : ℚ) / (2331102999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1310452719 / 1000000000000 : ℚ) + (66505043 / 40000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1583426441 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12154]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12154 :
    2 * 160 < 12154 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998303 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12154 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12155 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12155. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12155 : WorldParameters where
  hiddenCharge := (598814133 / 500000000000 : ℝ)
  frame := (633517284113 / 1000000000000 : ℝ)
  moment := (10579041561 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12155 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1500134975839 / 1000000000000 : ℝ)
    root := (7494669431 / 1000000000000 : ℝ) }

noncomputable def scalar12155 : ScalarCertificate 12155 world12155 agent12155 where
  dimensionLo := 12155
  dimensionHi := 12155
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2331506399 / 1000000000000 : ℝ)
  frameLo := (633517284113 / 1000000000000 : ℝ)
  frameHi := (1500134975839 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12155]
  agentFrame_pos := by norm_num only [agent12155]
  worldRadius := (2331506399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12155]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (5114369 / 3906250000 : ℝ)
  lowerTail := (51913907 / 31250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7913433359 / 1000000000000 : ℝ)
  ledger := by
    have h : (598814133 / 500000000000 : ℚ) +
        (10579041561 / 1000000000000000000 : ℚ) / (2331506399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (5114369 / 3906250000 : ℚ) + (51913907 / 31250000000 : ℚ) ≤
        (7913433359 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((598814133 / 500000000000 : ℚ) +
        (10579041561 / 1000000000000000000 : ℚ) / (2331506399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (5114369 / 3906250000 : ℚ) + (51913907 / 31250000000 : ℚ) : ℚ) : ℝ) ≤
        ((7913433359 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12155]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12155 :
    2 * 160 < 12155 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999299 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12155 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12156 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12156. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12156 : WorldParameters where
  hiddenCharge := (1197577731 / 1000000000000 : ℝ)
  frame := (126700428279 / 200000000000 : ℝ)
  moment := (2644190841 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12156 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (750043098621 / 500000000000 : ℝ)
    root := (7493998921 / 1000000000000 : ℝ) }

noncomputable def scalar12156 : ScalarCertificate 12156 world12156 agent12156 where
  dimensionLo := 12156
  dimensionHi := 12156
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2331909899 / 1000000000000 : ℝ)
  frameLo := (126700428279 / 200000000000 : ℝ)
  frameHi := (750043098621 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12156]
  agentFrame_pos := by norm_num only [agent12156]
  worldRadius := (2331909899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12156]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (654052789 / 500000000000 : ℝ)
  lowerTail := (1659865497 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7909738019 / 1000000000000 : ℝ)
  ledger := by
    have h : (1197577731 / 1000000000000 : ℚ) +
        (2644190841 / 250000000000000000 : ℚ) / (2331909899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (654052789 / 500000000000 : ℚ) + (1659865497 / 1000000000000 : ℚ) ≤
        (7909738019 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1197577731 / 1000000000000 : ℚ) +
        (2644190841 / 250000000000000000 : ℚ) / (2331909899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (654052789 / 500000000000 : ℚ) + (1659865497 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7909738019 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12156]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12156 :
    2 * 160 < 12156 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999587 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12156 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12157 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12157. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12157 : WorldParameters where
  hiddenCharge := (1197527209 / 1000000000000 : ℝ)
  frame := (633487001239 / 1000000000000 : ℝ)
  moment := (10574485853 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12157 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (750018723781 / 500000000000 : ℝ)
    root := (7493328547 / 1000000000000 : ℝ) }

noncomputable def scalar12157 : ScalarCertificate 12157 world12157 agent12157 where
  dimensionLo := 12157
  dimensionHi := 12157
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2332313299 / 1000000000000 : ℝ)
  frameLo := (633487001239 / 1000000000000 : ℝ)
  frameHi := (750018723781 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12157]
  agentFrame_pos := by norm_num only [agent12157]
  worldRadius := (2332313299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12157]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (40841681 / 31250000000 : ℝ)
  lowerTail := (1658487187 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (395302297 / 50000000000 : ℝ)
  ledger := by
    have h : (1197527209 / 1000000000000 : ℚ) +
        (10574485853 / 1000000000000000000 : ℚ) / (2332313299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (40841681 / 31250000000 : ℚ) + (1658487187 / 1000000000000 : ℚ) ≤
        (395302297 / 50000000000 : ℚ) := by norm_num only
    have hc : (((1197527209 / 1000000000000 : ℚ) +
        (10574485853 / 1000000000000000000 : ℚ) / (2332313299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (40841681 / 31250000000 : ℚ) + (1658487187 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((395302297 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12157]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12157 :
    2 * 160 < 12157 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999543 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12157 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12158 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12158. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12158 : WorldParameters where
  hiddenCharge := (598738351 / 500000000000 : ℝ)
  frame := (316735931823 / 500000000000 : ℝ)
  moment := (2643052257 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12158 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1499988726779 / 1000000000000 : ℝ)
    root := (3746329231 / 500000000000 : ℝ) }

noncomputable def scalar12158 : ScalarCertificate 12158 world12158 agent12158 where
  dimensionLo := 12158
  dimensionHi := 12158
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2332716799 / 1000000000000 : ℝ)
  frameLo := (316735931823 / 500000000000 : ℝ)
  frameHi := (1499988726779 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12158]
  agentFrame_pos := by norm_num only [agent12158]
  worldRadius := (2332716799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12158]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (326440843 / 250000000000 : ℝ)
  lowerTail := (414277599 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7902357361 / 1000000000000 : ℝ)
  ledger := by
    have h : (598738351 / 500000000000 : ℚ) +
        (2643052257 / 250000000000000000 : ℚ) / (2332716799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (326440843 / 250000000000 : ℚ) + (414277599 / 250000000000 : ℚ) ≤
        (7902357361 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((598738351 / 500000000000 : ℚ) +
        (2643052257 / 250000000000000000 : ℚ) / (2332716799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (326440843 / 250000000000 : ℚ) + (414277599 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7902357361 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12158]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12158 :
    2 * 160 < 12158 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998437 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12158 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding12134 :
    (1198692748454282612327 / 1000000000000000000000000 : ℝ) ≤ world12134.hiddenCharge ∧
    (316917937183742388671497 / 500000000000000000000000 : ℝ) ≤ world12134.frame ∧
    (10627042480186491 / 1000000000000000000000000 : ℝ) ≤ world12134.moment ∧
    (1501163896164801075119131 / 1000000000000000000000000 : ℝ) ≤ agent12134.frame ∧
    (3754399995169809899499 / 500000000000000000000000 : ℝ) ≤ agent12134.root ∧
    scalar12134.worldRadius ≤ (2323036999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1279422776318726705129 / 1000000000000000000000000 : ℝ) ≤ agent12134.charge ∧
    (166773947670035483079 / 125000000000000000000000 : ℝ) ≤ scalar12134.upperTail ∧
    (422631750317855920449 / 250000000000000000000000 : ℝ) ≤ scalar12134.lowerTail ∧
    scalar12134.totalBudget ≤ (7991804192340586404837 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12134, agent12134, scalar12134] <;> simp only [true_and]

theorem source_rounding12135 :
    (1198641918051922783409 / 1000000000000000000000000 : ℝ) ≤ world12135.hiddenCharge ∧
    (79227584709474779502991 / 125000000000000000000000 : ℝ) ≤ world12135.frame ∧
    (1328093728650211 / 125000000000000000000000 : ℝ) ≤ world12135.moment ∧
    (37527872037454234225711 / 25000000000000000000000 : ℝ) ≤ agent12135.frame ∧
    (3754062455300896372097 / 500000000000000000000000 : ℝ) ≤ agent12135.root ∧
    scalar12135.worldRadius ≤ (2323439999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (255819981404983255117 / 200000000000000000000000 : ℝ) ≤ agent12135.charge ∧
    (166624189858431144613 / 125000000000000000000000 : ℝ) ≤ scalar12135.upperTail ∧
    (844559916247740591007 / 500000000000000000000000 : ℝ) ≤ scalar12135.lowerTail ∧
    scalar12135.totalBudget ≤ (1597608073218757980601 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12135, agent12135, scalar12135] <;> simp only [true_and]

theorem source_rounding12136 :
    (599295550877834503599 / 500000000000000000000000 : ℝ) ≤ world12136.hiddenCharge ∧
    (633805483561232534436353 / 1000000000000000000000000 : ℝ) ≤ world12136.frame ∧
    (531122893459773 / 50000000000000000000000 : ℝ) ≤ world12136.moment ∧
    (750532945036865663694659 / 500000000000000000000000 : ℝ) ≤ agent12136.frame ∧
    (938431265350943533977 / 125000000000000000000000 : ℝ) ≤ agent12136.root ∧
    scalar12136.worldRadius ≤ (2323842799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (639388718528934464591 / 500000000000000000000000 : ℝ) ≤ agent12136.charge ∧
    (332949149606811086413 / 250000000000000000000000 : ℝ) ≤ scalar12136.upperTail ∧
    (1687713913592488248081 / 1000000000000000000000000 : ℝ) ≤ scalar12136.lowerTail ∧
    scalar12136.totalBudget ≤ (7984280062659218496651 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12136, agent12136, scalar12136] <;> simp only [true_and]

theorem source_rounding12137 :
    (599270149780197513449 / 500000000000000000000000 : ℝ) ≤ world12137.hiddenCharge ∧
    (633790292023091242722069 / 1000000000000000000000000 : ℝ) ≤ world12137.frame ∧
    (1327520824987551 / 125000000000000000000000 : ℝ) ≤ world12137.moment ∧
    (750508463965392602519447 / 500000000000000000000000 : ℝ) ≤ agent12137.frame ∧
    (3753387775119285504659 / 500000000000000000000000 : ℝ) ≤ agent12137.root ∧
    scalar12137.worldRadius ≤ (2324245699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (639227682913004124467 / 500000000000000000000000 : ℝ) ≤ agent12137.charge ∧
    (665300509285780482173 / 500000000000000000000000 : ℝ) ≤ scalar12137.upperTail ∧
    (1686309485423466927267 / 1000000000000000000000000 : ℝ) ≤ scalar12137.lowerTail ∧
    scalar12137.totalBudget ≤ (31173918800494700969 / 3906250000000000000000 : ℝ) := by
  norm_num only [world12137, agent12137, scalar12137] <;> simp only [true_and]

theorem source_rounding12138 :
    (1198489511460983703201 / 1000000000000000000000000 : ℝ) ≤ world12138.hiddenCharge ∧
    (633775103060677873714121 / 1000000000000000000000000 : ℝ) ≤ world12138.frame ∧
    (1061787602104953 / 100000000000000000000000 : ℝ) ≤ world12138.moment ∧
    (300193597798163111414761 / 200000000000000000000000 : ℝ) ≤ agent12138.frame ∧
    (7506101192753936828139 / 1000000000000000000000000 : ℝ) ≤ agent12138.root ∧
    scalar12138.worldRadius ≤ (2324648699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (255626738547753866959 / 200000000000000000000000 : ℝ) ≤ agent12138.charge ∧
    (1329406753083178827701 / 1000000000000000000000000 : ℝ) ≤ scalar12138.upperTail ∧
    (210613314248759384133 / 125000000000000000000000 : ℝ) ≤ scalar12138.lowerTail ∧
    scalar12138.totalBudget ≤ (3988384877400281568241 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12138, agent12138, scalar12138] <;> simp only [true_and]

theorem source_rounding12139 :
    (599219368726158115537 / 500000000000000000000000 : ℝ) ≤ world12139.hiddenCharge ∧
    (79219989584162039194787 / 125000000000000000000000 : ℝ) ≤ world12139.frame ∧
    (5307793066187897 / 500000000000000000000000 : ℝ) ≤ world12139.moment ∧
    (1500919085350705987166253 / 1000000000000000000000000 : ℝ) ≤ agent12139.frame ∧
    (11727229646430303253 / 1562500000000000000000 : ℝ) ≤ agent12139.root ∧
    scalar12139.worldRadius ≤ (2325051599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (159726552150824609113 / 125000000000000000000000 : ℝ) ≤ agent12139.charge ∧
    (83013352147777519221 / 62500000000000000000000 : ℝ) ≤ scalar12139.upperTail ∧
    (336700963389091301861 / 200000000000000000000000 : ℝ) ≤ scalar12139.lowerTail ∧
    scalar12139.totalBudget ≤ (3986509838146860014731 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12139, agent12139, scalar12139] <;> simp only [true_and]

theorem source_rounding12140 :
    (299596994382319718327 / 250000000000000000000000 : ℝ) ≤ world12140.hiddenCharge ∧
    (158436183215062648019703 / 250000000000000000000000 : ℝ) ≤ world12140.frame ∧
    (2653324233403101 / 250000000000000000000000 : ℝ) ≤ world12140.moment ∧
    (1500870017081710979166697 / 1000000000000000000000000 : ℝ) ≤ agent12140.frame ∧
    (7504753045993164456517 / 1000000000000000000000000 : ℝ) ≤ agent12140.root ∧
    scalar12140.worldRadius ≤ (2325454899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (79843221165058950553 / 62500000000000000000000 : ℝ) ≤ agent12140.charge ∧
    (1327021361619579983061 / 1000000000000000000000000 : ℝ) ≤ scalar12140.upperTail ∧
    (420525978293276144907 / 250000000000000000000000 : ℝ) ≤ scalar12140.lowerTail ∧
    scalar12140.totalBudget ≤ (249039729746918135401 / 31250000000000000000000 : ℝ) := by
  norm_num only [world12140, agent12140, scalar12140] <;> simp only [true_and]

theorem source_rounding12141 :
    (599168615843378787507 / 500000000000000000000000 : ℝ) ≤ world12141.hiddenCharge ∧
    (633729551620845285814813 / 1000000000000000000000000 : ℝ) ≤ world12141.frame ∧
    (10611008424492583 / 1000000000000000000000000 : ℝ) ≤ world12141.moment ∧
    (1500820814478064420727449 / 1000000000000000000000000 : ℝ) ≤ agent12141.frame ∧
    (1500815866586672347779 / 200000000000000000000000 : ℝ) ≤ agent12141.root ∧
    scalar12141.worldRadius ≤ (2325858299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (127717105645426642491 / 100000000000000000000000 : ℝ) ≤ agent12141.charge ∧
    (1325829764013102937687 / 1000000000000000000000000 : ℝ) ≤ scalar12141.upperTail ∧
    (1680703627496401514187 / 1000000000000000000000000 : ℝ) ≤ scalar12141.lowerTail ∧
    scalar12141.totalBudget ≤ (3982762470430854001591 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12141, agent12141, scalar12141] <;> simp only [true_and]

theorem source_rounding12142 :
    (299571624979910499983 / 250000000000000000000000 : ℝ) ≤ world12142.hiddenCharge ∧
    (633714372954384895563397 / 1000000000000000000000000 : ℝ) ≤ world12142.frame ∧
    (10608720604749741 / 1000000000000000000000000 : ℝ) ≤ world12142.moment ∧
    (750385823572687901464807 / 500000000000000000000000 : ℝ) ≤ agent12142.frame ∧
    (468962859871625665153 / 62500000000000000000000 : ℝ) ≤ agent12142.root ∧
    scalar12142.worldRadius ≤ (2326261799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (638425485030014210663 / 500000000000000000000000 : ℝ) ≤ agent12142.charge ∧
    (331159866547594526717 / 250000000000000000000000 : ℝ) ≤ scalar12142.upperTail ∧
    (167930479523825682721 / 100000000000000000000000 : ℝ) ≤ scalar12142.lowerTail ∧
    scalar12142.totalBudget ≤ (3980890952133519634047 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12142, agent12142, scalar12142] <;> simp only [true_and]

theorem source_rounding12143 :
    (599117891111412091339 / 500000000000000000000000 : ℝ) ≤ world12143.hiddenCharge ∧
    (633699196860174388505333 / 1000000000000000000000000 : ℝ) ≤ world12143.frame ∧
    (5303216737058707 / 500000000000000000000000 : ℝ) ≤ world12143.moment ∧
    (187590312111478346311313 / 125000000000000000000000 : ℝ) ≤ agent12143.frame ∧
    (1875683118451513375241 / 250000000000000000000000 : ℝ) ≤ agent12143.root ∧
    scalar12143.worldRadius ≤ (2326665099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (638265639436346500749 / 500000000000000000000000 : ℝ) ≤ agent12143.charge ∧
    (1323450277434631553261 / 1000000000000000000000000 : ℝ) ≤ scalar12143.upperTail ∧
    (335581434417026117547 / 200000000000000000000000 : ℝ) ≤ scalar12143.lowerTail ∧
    scalar12143.totalBudget ≤ (1989510577619207970283 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12143, agent12143, scalar12143] <;> simp only [true_and]

theorem source_rounding12144 :
    (1198185078591198527317 / 1000000000000000000000000 : ℝ) ≤ world12144.hiddenCharge ∧
    (633684023337518873400519 / 1000000000000000000000000 : ℝ) ≤ world12144.frame ∧
    (2651036758082317 / 250000000000000000000000 : ℝ) ≤ world12144.moment ∧
    (375168345467287393979993 / 250000000000000000000000 : ℝ) ≤ agent12144.frame ∧
    (937757425488486948313 / 125000000000000000000000 : ℝ) ≤ agent12144.root ∧
    scalar12144.worldRadius ≤ (2327068599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1276211982307723961207 / 1000000000000000000000000 : ℝ) ≤ agent12144.charge ∧
    (132226252178979105377 / 100000000000000000000000 : ℝ) ≤ scalar12144.upperTail ∧
    (419127788137777904843 / 250000000000000000000000 : ℝ) ≤ scalar12144.lowerTail ∧
    scalar12144.totalBudget ≤ (1988576551217393300037 / 250000000000000000000000 : ℝ) := by
  norm_num only [world12144, agent12144, scalar12144] <;> simp only [true_and]

theorem source_rounding12145 :
    (299533597254915116033 / 250000000000000000000000 : ℝ) ≤ world12145.hiddenCharge ∧
    (39604303274107737317501 / 62500000000000000000000 : ℝ) ≤ world12145.frame ∧
    (2650465319779761 / 250000000000000000000000 : ℝ) ≤ world12145.moment ∧
    (1500624296000084251434929 / 1000000000000000000000000 : ℝ) ≤ agent12145.frame ∧
    (3750693274055807463729 / 500000000000000000000000 : ℝ) ≤ agent12145.root ∧
    scalar12145.worldRadius ≤ (2327471899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (255178615956316636353 / 200000000000000000000000 : ℝ) ≤ agent12145.charge ∧
    (82567241402138788831 / 62500000000000000000000 : ℝ) ≤ scalar12145.upperTail ∧
    (837558170185845930471 / 500000000000000000000000 : ℝ) ≤ scalar12145.lowerTail ∧
    scalar12145.totalBudget ≤ (3975286762777118551583 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12145, agent12145, scalar12145] <;> simp only [true_and]

theorem source_rounding12146 :
    (599041856751554566891 / 500000000000000000000000 : ℝ) ≤ world12146.hiddenCharge ∧
    (2534614736016378953793 / 4000000000000000000000 : ℝ) ≤ world12146.frame ∧
    (2119915242844133 / 200000000000000000000000 : ℝ) ≤ world12146.moment ∧
    (750287619632324987620639 / 500000000000000000000000 : ℝ) ≤ agent12146.frame ∧
    (7500713829891488091073 / 1000000000000000000000000 : ℝ) ≤ agent12146.root ∧
    scalar12146.worldRadius ≤ (2327875499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (39861705334741522723 / 31250000000000000000000 : ℝ) ≤ agent12146.charge ∧
    (329972656888870866769 / 250000000000000000000000 : ℝ) ≤ scalar12146.upperTail ∧
    (836861562048769728069 / 500000000000000000000000 : ℝ) ≤ scalar12146.lowerTail ∧
    scalar12146.totalBudget ≤ (7946844149033425416763 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12146, agent12146, scalar12146] <;> simp only [true_and]

theorem source_rounding12147 :
    (1198033052036444701597 / 1000000000000000000000000 : ℝ) ≤ world12147.hiddenCharge ∧
    (316819259095968873561263 / 500000000000000000000000 : ℝ) ≤ world12147.frame ∧
    (165582684958877 / 15625000000000000000000 : ℝ) ≤ world12147.moment ∧
    (750263102793513697548047 / 500000000000000000000000 : ℝ) ≤ agent12147.frame ∧
    (1500008280379128740691 / 200000000000000000000000 : ℝ) ≤ agent12147.root ∧
    scalar12147.worldRadius ≤ (2328278899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (255051290903322589 / 200000000000000000000 : ℝ) ≤ agent12147.charge ∧
    (131870652024778425469 / 100000000000000000000000 : ℝ) ≤ scalar12147.upperTail ∧
    (1672331142775798511329 / 1000000000000000000000000 : ℝ) ≤ scalar12147.lowerTail ∧
    scalar12147.totalBudget ≤ (496444891059639394283 / 62500000000000000000000 : ℝ) := by
  norm_num only [world12147, agent12147, scalar12147] <;> simp only [true_and]

theorem source_rounding12148 :
    (598991202307285519579 / 500000000000000000000000 : ℝ) ≤ world12148.hiddenCharge ∧
    (3960145968428493247567 / 6250000000000000000000 : ℝ) ≤ world12148.frame ∧
    (165547002317119 / 15625000000000000000000 : ℝ) ≤ world12148.moment ∧
    (300095441411857941040231 / 200000000000000000000000 : ℝ) ≤ agent12148.frame ∧
    (299974767503310360697 / 40000000000000000000000 : ℝ) ≤ agent12148.root ∧
    scalar12148.worldRadius ≤ (2328682199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1274938730615680571751 / 1000000000000000000000000 : ℝ) ≤ agent12148.charge ∧
    (1317523606904345772057 / 1000000000000000000000000 : ℝ) ≤ scalar12148.upperTail ∧
    (417735121698906204913 / 250000000000000000000000 : ℝ) ≤ scalar12148.lowerTail ∧
    scalar12148.totalBudget ≤ (248106119916121160323 / 31250000000000000000000 : ℝ) := by
  norm_num only [world12148, agent12148, scalar12148] <;> simp only [true_and]

theorem source_rounding12149 :
    (598965885616197190209 / 500000000000000000000000 : ℝ) ≤ world12149.hiddenCharge ∧
    (316804097136632371156637 / 500000000000000000000000 : ℝ) ≤ world12149.frame ∧
    (2118545029347487 / 200000000000000000000000 : ℝ) ≤ world12149.moment ∧
    (75021411577504055537387 / 50000000000000000000000 : ℝ) ≤ agent12149.frame ∧
    (937337138809408657363 / 125000000000000000000000 : ℝ) ≤ agent12149.root ∧
    scalar12149.worldRadius ≤ (2329085799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1274621398429366841431 / 1000000000000000000000000 : ℝ) ≤ agent12149.charge ∧
    (1316342088807462706223 / 1000000000000000000000000 : ℝ) ≤ scalar12149.upperTail ∧
    (1669551389551143509161 / 1000000000000000000000000 : ℝ) ≤ scalar12149.lowerTail ∧
    scalar12149.totalBudget ≤ (7935676652467824335759 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12149, agent12149, scalar12149] <;> simp only [true_and]

theorem source_rounding12150 :
    (598940575942410321553 / 500000000000000000000000 : ℝ) ≤ world12150.hiddenCharge ∧
    (633593036165361826851139 / 1000000000000000000000000 : ℝ) ≤ world12150.frame ∧
    (5295221416213959 / 500000000000000000000000 : ℝ) ≤ world12150.moment ∧
    (1500379285095382779378857 / 1000000000000000000000000 : ℝ) ≤ agent12150.frame ∧
    (3749012661563123691969 / 500000000000000000000000 : ℝ) ≤ agent12150.root ∧
    scalar12150.worldRadius ≤ (2329489199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1274304457379095598571 / 1000000000000000000000000 : ℝ) ≤ agent12150.charge ∧
    (1315161718247425746409 / 1000000000000000000000000 : ℝ) ≤ scalar12150.upperTail ∧
    (1668163554627543250673 / 1000000000000000000000000 : ℝ) ≤ scalar12150.lowerTail ∧
    scalar12150.totalBudget ≤ (3965980498471716828291 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12150, agent12150, scalar12150] <;> simp only [true_and]

theorem source_rounding12151 :
    (1197830546566760785551 / 1000000000000000000000000 : ℝ) ≤ world12151.hiddenCharge ∧
    (126715576124831435974159 / 200000000000000000000000 : ℝ) ≤ world12151.frame ∧
    (10588161205101629 / 1000000000000000000000000 : ℝ) ≤ world12151.moment ∧
    (23442661994927144092677 / 15625000000000000000000 : ℝ) ≤ agent12151.frame ∧
    (3748676874521272193997 / 500000000000000000000000 : ℝ) ≤ agent12151.root ∧
    scalar12151.worldRadius ≤ (2329892599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (636993953443638707479 / 500000000000000000000000 : ℝ) ≤ agent12151.charge ∧
    (656991295115838791557 / 500000000000000000000000 : ℝ) ≤ scalar12151.upperTail ∧
    (1666777098620532908583 / 1000000000000000000000000 : ℝ) ≤ scalar12151.lowerTail ∧
    scalar12151.totalBudget ≤ (7928248746505532301123 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12151, agent12151, scalar12151] <;> simp only [true_and]

theorem source_rounding12152 :
    (1197779955273126786909 / 1000000000000000000000000 : ℝ) ≤ world12152.hiddenCharge ∧
    (633562727648958012964073 / 1000000000000000000000000 : ℝ) ≤ world12152.frame ∧
    (10585880264493209 / 1000000000000000000000000 : ℝ) ≤ world12152.moment ∧
    (1500281479270111625883811 / 1000000000000000000000000 : ℝ) ≤ agent12152.frame ∧
    (7496682311794703823181 / 1000000000000000000000000 : ℝ) ≤ agent12152.root ∧
    scalar12152.worldRadius ≤ (2330295999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (127367174637730771029 / 100000000000000000000000 : ℝ) ≤ agent12152.charge ∧
    (1312804645100884624023 / 1000000000000000000000000 : ℝ) ≤ scalar12152.upperTail ∧
    (1665391957648518890131 / 1000000000000000000000000 : ℝ) ≤ scalar12152.lowerTail ∧
    scalar12152.totalBudget ≤ (3962269887690572345893 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12152, agent12152, scalar12152] <;> simp only [true_and]

theorem source_rounding12153 :
    (598864688999417161151 / 500000000000000000000000 : ℝ) ≤ world12153.hiddenCharge ∧
    (316773788619535859484377 / 500000000000000000000000 : ℝ) ≤ world12153.frame ∧
    (264590000258437 / 25000000000000000000000 : ℝ) ≤ world12153.moment ∧
    (1500232613805698027687221 / 1000000000000000000000000 : ℝ) ≤ agent12153.frame ∧
    (7496011163840838655759 / 1000000000000000000000000 : ℝ) ≤ agent12153.root ∧
    scalar12153.worldRadius ≤ (2330699499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1273355975273564876741 / 1000000000000000000000000 : ℝ) ≤ agent12153.charge ∧
    (1311628050621633830237 / 1000000000000000000000000 : ℝ) ≤ scalar12153.upperTail ∧
    (1664008312919677079801 / 1000000000000000000000000 : ℝ) ≤ scalar12153.lowerTail ∧
    scalar12153.totalBudget ≤ (7920834266126825662921 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12153, agent12153, scalar12153] <;> simp only [true_and]

theorem source_rounding12154 :
    (119767881473879875013 / 100000000000000000000000 : ℝ) ≤ world12154.hiddenCharge ∧
    (633532429393806075102003 / 1000000000000000000000000 : ℝ) ≤ world12154.frame ∧
    (5290660221184643 / 500000000000000000000000 : ℝ) ≤ world12154.moment ∧
    (750091891685494558568561 / 500000000000000000000000 : ℝ) ≤ agent12154.frame ∧
    (7495340228735923273643 / 1000000000000000000000000 : ℝ) ≤ agent12154.root ∧
    scalar12154.worldRadius ≤ (2331102999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (254608118600281681479 / 200000000000000000000000 : ℝ) ≤ agent12154.charge ∧
    (655226359119899254039 / 500000000000000000000000 : ℝ) ≤ scalar12154.upperTail ∧
    (207828259250933713149 / 125000000000000000000000 : ℝ) ≤ scalar12154.lowerTail ∧
    scalar12154.totalBudget ≤ (989641525745810564397 / 125000000000000000000000 : ℝ) := by
  norm_num only [world12154, agent12154, scalar12154] <;> simp only [true_and]

theorem source_rounding12155 :
    (1197628265487940458599 / 1000000000000000000000000 : ℝ) ≤ world12155.hiddenCharge ∧
    (316758642056234517238181 / 500000000000000000000000 : ℝ) ≤ world12155.frame ∧
    (1322380195040463 / 125000000000000000000000 : ℝ) ≤ world12155.moment ∧
    (12001079806704821461873 / 8000000000000000000000 : ℝ) ≤ agent12155.frame ∧
    (7494669430098559298683 / 1000000000000000000000000 : ℝ) ≤ agent12155.root ∧
    scalar12155.worldRadius ≤ (2331506399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1272725598987177028563 / 1000000000000000000000000 : ℝ) ≤ agent12155.charge ∧
    (654639231526414314233 / 500000000000000000000000 : ℝ) ≤ scalar12155.upperTail ∧
    (830622511835492545391 / 500000000000000000000000 : ℝ) ≤ scalar12155.lowerTail ∧
    scalar12155.totalBudget ≤ (791343335947151255193 / 100000000000000000000000 : ℝ) := by
  norm_num only [world12155, agent12155, scalar12155] <;> simp only [true_and]

theorem source_rounding12156 :
    (239515546048235903789 / 200000000000000000000000 : ℝ) ≤ world12156.hiddenCharge ∧
    (158375535348592189672927 / 250000000000000000000000 : ℝ) ≤ world12156.frame ∧
    (2115352672787167 / 200000000000000000000000 : ℝ) ≤ world12156.moment ∧
    (750043098620751788852693 / 500000000000000000000000 : ℝ) ≤ agent12156.frame ∧
    (749399892029199525831 / 100000000000000000000000 : ℝ) ≤ agent12156.root ∧
    scalar12156.worldRadius ≤ (2331909899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (50896439706327473439 / 40000000000000000000000 : ℝ) ≤ agent12156.charge ∧
    (327026394467987521613 / 250000000000000000000000 : ℝ) ≤ scalar12156.upperTail ∧
    (41496637406977357009 / 25000000000000000000000 : ℝ) ≤ scalar12156.lowerTail ∧
    scalar12156.totalBudget ≤ (7909738019588913142261 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12156, agent12156, scalar12156] <;> simp only [true_and]

theorem source_rounding12157 :
    (47901088359737641073 / 40000000000000000000000 : ℝ) ≤ world12157.hiddenCharge ∧
    (633487001238813807408767 / 1000000000000000000000000 : ℝ) ≤ world12157.frame ∧
    (10574485852941013 / 1000000000000000000000000 : ℝ) ≤ world12157.moment ∧
    (375009361890370344716177 / 250000000000000000000000 : ℝ) ≤ agent12157.frame ∧
    (1873332136677038563833 / 250000000000000000000000 : ℝ) ≤ agent12157.root ∧
    scalar12157.worldRadius ≤ (2332313299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (636048386721364717411 / 500000000000000000000000 : ℝ) ≤ agent12157.charge ∧
    (26138675826082505313 / 20000000000000000000000 : ℝ) ≤ scalar12157.upperTail ∧
    (1658487186329527865789 / 1000000000000000000000000 : ℝ) ≤ scalar12157.lowerTail ∧
    scalar12157.totalBudget ≤ (1581209188192292956261 / 200000000000000000000000 : ℝ) := by
  norm_num only [world12157, agent12157, scalar12157] <;> simp only [true_and]

theorem source_rounding12158 :
    (1197476701739649760681 / 1000000000000000000000000 : ℝ) ≤ world12158.hiddenCharge ∧
    (633471863645112899208469 / 1000000000000000000000000 : ℝ) ≤ world12158.frame ∧
    (10572209027074593 / 1000000000000000000000000 : ℝ) ≤ world12158.moment ∧
    (749994363389175075700653 / 500000000000000000000000 : ℝ) ≤ agent12158.frame ∧
    (1498531692329403802201 / 200000000000000000000000 : ℝ) ≤ agent12158.root ∧
    scalar12158.worldRadius ≤ (2332716799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1271782940770070083651 / 1000000000000000000000000 : ℝ) ≤ agent12158.charge ∧
    (26115267429910274331 / 20000000000000000000000 : ℝ) ≤ scalar12158.upperTail ∧
    (414277598972580165189 / 250000000000000000000000 : ℝ) ≤ scalar12158.lowerTail ∧
    scalar12158.totalBudget ≤ (3951178680531889260773 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12158, agent12158, scalar12158] <;> simp only [true_and]

noncomputable def paperAgent12134 : AgentParameters :=
  { agent12134 with charge := (63971139 / 50000000000 : ℝ) }

theorem agent_is_repriced12134 : agent12134 =
    BstLean.Part265.agentRepriced 12134 world12134 paperAgent12134 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12134, agent12134]

noncomputable def paperAgent12135 : AgentParameters :=
  { agent12135 with charge := (1279099911 / 1000000000000 : ℝ) }

theorem agent_is_repriced12135 : agent12135 =
    BstLean.Part265.agentRepriced 12135 world12135 paperAgent12135 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12135, agent12135]

noncomputable def paperAgent12136 : AgentParameters :=
  { agent12136 with charge := (1278777441 / 1000000000000 : ℝ) }

theorem agent_is_repriced12136 : agent12136 =
    BstLean.Part265.agentRepriced 12136 world12136 paperAgent12136 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12136, agent12136]

noncomputable def paperAgent12137 : AgentParameters :=
  { agent12137 with charge := (1278455369 / 1000000000000 : ℝ) }

theorem agent_is_repriced12137 : agent12137 =
    BstLean.Part265.agentRepriced 12137 world12137 paperAgent12137 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12137, agent12137]

noncomputable def paperAgent12138 : AgentParameters :=
  { agent12138 with charge := (19970839 / 15625000000 : ℝ) }

theorem agent_is_repriced12138 : agent12138 =
    BstLean.Part265.agentRepriced 12138 world12138 paperAgent12138 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12138, agent12138]

noncomputable def paperAgent12139 : AgentParameters :=
  { agent12139 with charge := (1277812421 / 1000000000000 : ℝ) }

theorem agent_is_repriced12139 : agent12139 =
    BstLean.Part265.agentRepriced 12139 world12139 paperAgent12139 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12139, agent12139]

noncomputable def paperAgent12140 : AgentParameters :=
  { agent12140 with charge := (638745771 / 500000000000 : ℝ) }

theorem agent_is_repriced12140 : agent12140 =
    BstLean.Part265.agentRepriced 12140 world12140 paperAgent12140 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12140, agent12140]

noncomputable def paperAgent12141 : AgentParameters :=
  { agent12141 with charge := (63858553 / 50000000000 : ℝ) }

theorem agent_is_repriced12141 : agent12141 =
    BstLean.Part265.agentRepriced 12141 world12141 paperAgent12141 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12141, agent12141]

noncomputable def paperAgent12142 : AgentParameters :=
  { agent12142 with charge := (1276850973 / 1000000000000 : ℝ) }

theorem agent_is_repriced12142 : agent12142 =
    BstLean.Part265.agentRepriced 12142 world12142 paperAgent12142 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12142, agent12142]

noncomputable def paperAgent12143 : AgentParameters :=
  { agent12143 with charge := (638265641 / 500000000000 : ℝ) }

theorem agent_is_repriced12143 : agent12143 =
    BstLean.Part265.agentRepriced 12143 world12143 paperAgent12143 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12143, agent12143]

noncomputable def paperAgent12144 : AgentParameters :=
  { agent12144 with charge := (255242397 / 200000000000 : ℝ) }

theorem agent_is_repriced12144 : agent12144 =
    BstLean.Part265.agentRepriced 12144 world12144 paperAgent12144 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12144, agent12144]

noncomputable def paperAgent12145 : AgentParameters :=
  { agent12145 with charge := (1275893083 / 1000000000000 : ℝ) }

theorem agent_is_repriced12145 : agent12145 =
    BstLean.Part265.agentRepriced 12145 world12145 paperAgent12145 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12145, agent12145]

noncomputable def paperAgent12146 : AgentParameters :=
  { agent12146 with charge := (637787287 / 500000000000 : ℝ) }

theorem agent_is_repriced12146 : agent12146 =
    BstLean.Part265.agentRepriced 12146 world12146 paperAgent12146 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12146, agent12146]

noncomputable def paperAgent12147 : AgentParameters :=
  { agent12147 with charge := (637628229 / 500000000000 : ℝ) }

theorem agent_is_repriced12147 : agent12147 =
    BstLean.Part265.agentRepriced 12147 world12147 paperAgent12147 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12147, agent12147]

noncomputable def paperAgent12148 : AgentParameters :=
  { agent12148 with charge := (637469367 / 500000000000 : ℝ) }

theorem agent_is_repriced12148 : agent12148 =
    BstLean.Part265.agentRepriced 12148 world12148 paperAgent12148 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12148, agent12148]

noncomputable def paperAgent12149 : AgentParameters :=
  { agent12149 with charge := (637310701 / 500000000000 : ℝ) }

theorem agent_is_repriced12149 : agent12149 =
    BstLean.Part265.agentRepriced 12149 world12149 paperAgent12149 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12149, agent12149]

noncomputable def paperAgent12150 : AgentParameters :=
  { agent12150 with charge := (1274304461 / 1000000000000 : ℝ) }

theorem agent_is_repriced12150 : agent12150 =
    BstLean.Part265.agentRepriced 12150 world12150 paperAgent12150 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12150, agent12150]

noncomputable def paperAgent12151 : AgentParameters :=
  { agent12151 with charge := (127398791 / 100000000000 : ℝ) }

theorem agent_is_repriced12151 : agent12151 =
    BstLean.Part265.agentRepriced 12151 world12151 paperAgent12151 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12151, agent12151]

noncomputable def paperAgent12152 : AgentParameters :=
  { agent12152 with charge := (5094687 / 4000000000 : ℝ) }

theorem agent_is_repriced12152 : agent12152 =
    BstLean.Part265.agentRepriced 12152 world12152 paperAgent12152 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12152, agent12152]

noncomputable def paperAgent12153 : AgentParameters :=
  { agent12153 with charge := (1273355979 / 1000000000000 : ℝ) }

theorem agent_is_repriced12153 : agent12153 =
    BstLean.Part265.agentRepriced 12153 world12153 paperAgent12153 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12153, agent12153]

noncomputable def paperAgent12154 : AgentParameters :=
  { agent12154 with charge := (1273040597 / 1000000000000 : ℝ) }

theorem agent_is_repriced12154 : agent12154 =
    BstLean.Part265.agentRepriced 12154 world12154 paperAgent12154 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12154, agent12154]

noncomputable def paperAgent12155 : AgentParameters :=
  { agent12155 with charge := (1272725603 / 1000000000000 : ℝ) }

theorem agent_is_repriced12155 : agent12155 =
    BstLean.Part265.agentRepriced 12155 world12155 paperAgent12155 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12155, agent12155]

noncomputable def paperAgent12156 : AgentParameters :=
  { agent12156 with charge := (318102749 / 250000000000 : ℝ) }

theorem agent_is_repriced12156 : agent12156 =
    BstLean.Part265.agentRepriced 12156 world12156 paperAgent12156 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12156, agent12156]

noncomputable def paperAgent12157 : AgentParameters :=
  { agent12157 with charge := (1272096777 / 1000000000000 : ℝ) }

theorem agent_is_repriced12157 : agent12157 =
    BstLean.Part265.agentRepriced 12157 world12157 paperAgent12157 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12157, agent12157]

noncomputable def paperAgent12158 : AgentParameters :=
  { agent12158 with charge := (39743217 / 31250000000 : ℝ) }

theorem agent_is_repriced12158 : agent12158 =
    BstLean.Part265.agentRepriced 12158 world12158 paperAgent12158 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12158, agent12158]

end BstLean.Part281
