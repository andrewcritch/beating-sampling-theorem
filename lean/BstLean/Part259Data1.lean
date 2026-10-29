import BstLean.Part243Row

#eval (do IO.println s!"p259-row-start 12230 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12230. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12230 : WorldParameters where
  hiddenCharge := (119387663 / 100000000000 : ℝ)
  frame := (158097161237 / 250000000000 : ℝ)
  moment := (10410061081 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12230 : AgentParameters :=
  { agentLedgerParameters with
    charge := (238305897 / 125000000000 : ℝ)
    frame := (1459835043023 / 1000000000000 : ℝ)
    root := (1105764513 / 125000000000 : ℝ) }

noncomputable def scalar12230 : ScalarCertificate 12230 world12230 agent12230 where
  dimensionLo := 12230
  dimensionHi := 12230
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2050225099 / 1000000000000 : ℝ)
  frameLo := (158097161237 / 250000000000 : ℝ)
  frameHi := (1459835043023 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12230]
  agentFrame_pos := by norm_num only [agent12230]
  worldRadius := (2050225099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12230]
  retainedCharge := (238305897 / 125000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1025506541 / 500000000000 : ℝ)
  lowerTail := (14618311 / 6250000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1993367047 / 200000000000 : ℝ)
  ledger := by
    have h : (119387663 / 100000000000 : ℚ) +
        (10410061081 / 1000000000000000000 : ℚ) / (2050225099 / 1000000000000 : ℚ) ^ 2 +
        (238305897 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1025506541 / 500000000000 : ℚ) + (14618311 / 6250000000 : ℚ) ≤
        (1993367047 / 200000000000 : ℚ) := by norm_num only
    have hc : (((119387663 / 100000000000 : ℚ) +
        (10410061081 / 1000000000000000000 : ℚ) / (2050225099 / 1000000000000 : ℚ) ^ 2 +
        (238305897 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1025506541 / 500000000000 : ℚ) + (14618311 / 6250000000 : ℚ) : ℚ) : ℝ) ≤
        ((1993367047 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12230]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12230 :
    2 * 160 < 12230 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2199999799 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12230 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12231 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12231. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12231 : WorldParameters where
  hiddenCharge := (1193827131 / 1000000000000 : ℝ)
  frame := (15809342313 / 25000000000 : ℝ)
  moment := (10407833563 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12231 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1905687209 / 1000000000000 : ℝ)
    frame := (145979354591 / 100000000000 : ℝ)
    root := (221134301 / 25000000000 : ℝ) }

noncomputable def scalar12231 : ScalarCertificate 12231 world12231 agent12231 where
  dimensionLo := 12231
  dimensionHi := 12231
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2050579399 / 1000000000000 : ℝ)
  frameLo := (15809342313 / 25000000000 : ℝ)
  frameHi := (145979354591 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12231]
  agentFrame_pos := by norm_num only [agent12231]
  worldRadius := (2050579399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12231]
  retainedCharge := (1905687209 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (25614827 / 12500000000 : ℝ)
  lowerTail := (467396583 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (398434661 / 40000000000 : ℝ)
  ledger := by
    have h : (1193827131 / 1000000000000 : ℚ) +
        (10407833563 / 1000000000000000000 : ℚ) / (2050579399 / 1000000000000 : ℚ) ^ 2 +
        (1905687209 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (25614827 / 12500000000 : ℚ) + (467396583 / 200000000000 : ℚ) ≤
        (398434661 / 40000000000 : ℚ) := by norm_num only
    have hc : (((1193827131 / 1000000000000 : ℚ) +
        (10407833563 / 1000000000000000000 : ℚ) / (2050579399 / 1000000000000 : ℚ) ^ 2 +
        (1905687209 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (25614827 / 12500000000 : ℚ) + (467396583 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((398434661 / 40000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12231]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12231 :
    2 * 160 < 12231 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2199999321 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12231 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12232 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12232. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12232 : WorldParameters where
  hiddenCharge := (238755529 / 200000000000 : ℝ)
  frame := (632358742603 / 1000000000000 : ℝ)
  moment := (10405606711 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12232 : AgentParameters :=
  { agentLedgerParameters with
    charge := (190492793 / 100000000000 : ℝ)
    frame := (36493801599 / 25000000000 : ℝ)
    root := (8844628213 / 1000000000000 : ℝ) }

noncomputable def scalar12232 : ScalarCertificate 12232 world12232 agent12232 where
  dimensionLo := 12232
  dimensionHi := 12232
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2050933699 / 1000000000000 : ℝ)
  frameLo := (632358742603 / 1000000000000 : ℝ)
  frameHi := (36493801599 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12232]
  agentFrame_pos := by norm_num only [agent12232]
  worldRadius := (2050933699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12232]
  retainedCharge := (190492793 / 100000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (2047361067 / 1000000000000 : ℝ)
  lowerTail := (2335037909 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9954903151 / 1000000000000 : ℝ)
  ledger := by
    have h : (238755529 / 200000000000 : ℚ) +
        (10405606711 / 1000000000000000000 : ℚ) / (2050933699 / 1000000000000 : ℚ) ^ 2 +
        (190492793 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2047361067 / 1000000000000 : ℚ) + (2335037909 / 1000000000000 : ℚ) ≤
        (9954903151 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((238755529 / 200000000000 : ℚ) +
        (10405606711 / 1000000000000000000 : ℚ) / (2050933699 / 1000000000000 : ℚ) ^ 2 +
        (190492793 / 100000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (2047361067 / 1000000000000 : ℚ) + (2335037909 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9954903151 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12232]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12232 :
    2 * 160 < 12232 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (1374999911 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12232 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12233 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12233. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12233 : WorldParameters where
  hiddenCharge := (1193728173 / 1000000000000 : ℝ)
  frame := (632343795197 / 1000000000000 : ℝ)
  moment := (416135221 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12233 : AgentParameters :=
  { agentLedgerParameters with
    charge := (952084669 / 500000000000 : ℝ)
    frame := (145971060893 / 100000000000 : ℝ)
    root := (4421942311 / 500000000000 : ℝ) }

noncomputable def scalar12233 : ScalarCertificate 12233 world12233 agent12233 where
  dimensionLo := 12233
  dimensionHi := 12233
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2051288099 / 1000000000000 : ℝ)
  frameLo := (632343795197 / 1000000000000 : ℝ)
  frameHi := (145971060893 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12233]
  agentFrame_pos := by norm_num only [agent12233]
  worldRadius := (2051288099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12233]
  retainedCharge := (952084669 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (511384497 / 250000000000 : ℝ)
  lowerTail := (1166547473 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9948945261 / 1000000000000 : ℝ)
  ledger := by
    have h : (1193728173 / 1000000000000 : ℚ) +
        (416135221 / 40000000000000000 : ℚ) / (2051288099 / 1000000000000 : ℚ) ^ 2 +
        (952084669 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (511384497 / 250000000000 : ℚ) + (1166547473 / 500000000000 : ℚ) ≤
        (9948945261 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1193728173 / 1000000000000 : ℚ) +
        (416135221 / 40000000000000000 : ℚ) / (2051288099 / 1000000000000 : ℚ) ^ 2 +
        (952084669 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (511384497 / 250000000000 : ℚ) + (1166547473 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9948945261 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12233]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12233 :
    2 * 160 < 12233 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (10999995113 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12233 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12234 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12234. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part259
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12234 : WorldParameters where
  hiddenCharge := (238735743 / 200000000000 : ℝ)
  frame := (6323288503 / 10000000000 : ℝ)
  moment := (2600288751 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12234 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1903411431 / 1000000000000 : ℝ)
    frame := (1459669169043 / 1000000000000 : ℝ)
    root := (8843141269 / 1000000000000 : ℝ) }

noncomputable def scalar12234 : ScalarCertificate 12234 world12234 agent12234 where
  dimensionLo := 12234
  dimensionHi := 12234
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2051642399 / 1000000000000 : ℝ)
  frameLo := (6323288503 / 10000000000 : ℝ)
  frameHi := (1459669169043 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12234]
  agentFrame_pos := by norm_num only [agent12234]
  worldRadius := (2051642399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12234]
  retainedCharge := (1903411431 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (255464577 / 125000000000 : ℝ)
  lowerTail := (2331153693 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9942992697 / 1000000000000 : ℝ)
  ledger := by
    have h : (238735743 / 200000000000 : ℚ) +
        (2600288751 / 250000000000000000 : ℚ) / (2051642399 / 1000000000000 : ℚ) ^ 2 +
        (1903411431 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (255464577 / 125000000000 : ℚ) + (2331153693 / 1000000000000 : ℚ) ≤
        (9942992697 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((238735743 / 200000000000 : ℚ) +
        (2600288751 / 250000000000000000 : ℚ) / (2051642399 / 1000000000000 : ℚ) ^ 2 +
        (1903411431 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (255464577 / 125000000000 : ℚ) + (2331153693 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9942992697 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12234]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12234 :
    2 * 160 < 12234 - 1 ∧
    (0 : ℝ) < (1113 / 500000 : ℝ) ∧ (1113 / 500000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (6787 / 31250 : ℝ) ∧
    (2199999191 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part259

#eval (do IO.println s!"p259-row-end 12234 {← IO.monoMsNow}" : IO Unit)
