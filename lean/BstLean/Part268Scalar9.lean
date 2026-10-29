import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12575 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12575. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12575 : WorldParameters where
  hiddenCharge := (1177575809 / 1000000000000 : ℝ)
  frame := (31368732969 / 50000000000 : ℝ)
  moment := (9679415091 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12575 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (740622478877 / 500000000000 : ℝ)
    root := (214560883 / 25000000000 : ℝ) }

noncomputable def scalar12575 : ScalarCertificate 12575 world12575 agent12575 where
  dimensionLo := 12575
  dimensionHi := 12575
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2131235899 / 1000000000000 : ℝ)
  frameLo := (31368732969 / 50000000000 : ℝ)
  frameHi := (740622478877 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12575]
  agentFrame_pos := by norm_num only [agent12575]
  worldRadius := (2131235899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12575]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1625519351 / 1000000000000 : ℝ)
  lowerTail := (1906821887 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8640075891 / 1000000000000 : ℝ)
  ledger := by
    have h : (1177575809 / 1000000000000 : ℚ) +
        (9679415091 / 1000000000000000000 : ℚ) / (2131235899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1625519351 / 1000000000000 : ℚ) + (1906821887 / 1000000000000 : ℚ) ≤
        (8640075891 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1177575809 / 1000000000000 : ℚ) +
        (9679415091 / 1000000000000000000 : ℚ) / (2131235899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1625519351 / 1000000000000 : ℚ) + (1906821887 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8640075891 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12575]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12575 :
    2 * 160 < 12575 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999181 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12575 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12576 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12576. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12576 : WorldParameters where
  hiddenCharge := (1177530733 / 1000000000000 : ℝ)
  frame := (125472107017 / 200000000000 : ℝ)
  moment := (4838701461 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12576 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1481211413843 / 1000000000000 : ℝ)
    root := (1716346641 / 200000000000 : ℝ) }

noncomputable def scalar12576 : ScalarCertificate 12576 world12576 agent12576 where
  dimensionLo := 12576
  dimensionHi := 12576
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2131589099 / 1000000000000 : ℝ)
  frameLo := (125472107017 / 200000000000 : ℝ)
  frameHi := (1481211413843 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12576]
  agentFrame_pos := by norm_num only [agent12576]
  worldRadius := (2131589099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12576]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1624127081 / 1000000000000 : ℝ)
  lowerTail := (1905304457 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8635972113 / 1000000000000 : ℝ)
  ledger := by
    have h : (1177530733 / 1000000000000 : ℚ) +
        (4838701461 / 500000000000000000 : ℚ) / (2131589099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1624127081 / 1000000000000 : ℚ) + (1905304457 / 1000000000000 : ℚ) ≤
        (8635972113 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1177530733 / 1000000000000 : ℚ) +
        (4838701461 / 500000000000000000 : ℚ) / (2131589099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1624127081 / 1000000000000 : ℚ) + (1905304457 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8635972113 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12576]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12576 :
    2 * 160 < 12576 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997153 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12576 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12577 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12577. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12577 : WorldParameters where
  hiddenCharge := (117748567 / 100000000000 : ℝ)
  frame := (313673206541 / 500000000000 : ℝ)
  moment := (9675391337 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12577 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1481177891353 / 1000000000000 : ℝ)
    root := (4290515653 / 500000000000 : ℝ) }

noncomputable def scalar12577 : ScalarCertificate 12577 world12577 agent12577 where
  dimensionLo := 12577
  dimensionHi := 12577
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2131942399 / 1000000000000 : ℝ)
  frameLo := (313673206541 / 500000000000 : ℝ)
  frameHi := (1481177891353 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12577]
  agentFrame_pos := by norm_num only [agent12577]
  worldRadius := (2131942399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12577]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1622736299 / 1000000000000 : ℝ)
  lowerTail := (951894283 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2157967987 / 250000000000 : ℝ)
  ledger := by
    have h : (117748567 / 100000000000 : ℚ) +
        (9675391337 / 1000000000000000000 : ℚ) / (2131942399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1622736299 / 1000000000000 : ℚ) + (951894283 / 500000000000 : ℚ) ≤
        (2157967987 / 250000000000 : ℚ) := by norm_num only
    have hc : (((117748567 / 100000000000 : ℚ) +
        (9675391337 / 1000000000000000000 : ℚ) / (2131942399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1622736299 / 1000000000000 : ℚ) + (951894283 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2157967987 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12577]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12577 :
    2 * 160 < 12577 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (439999841 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12577 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12578 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12578. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12578 : WorldParameters where
  hiddenCharge := (588720309 / 500000000000 : ℝ)
  frame := (627332293373 / 1000000000000 : ℝ)
  moment := (604586271 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12578 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (740572192163 / 500000000000 : ℝ)
    root := (8580329623 / 1000000000000 : ℝ) }

noncomputable def scalar12578 : ScalarCertificate 12578 world12578 agent12578 where
  dimensionLo := 12578
  dimensionHi := 12578
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2132295599 / 1000000000000 : ℝ)
  frameLo := (627332293373 / 1000000000000 : ℝ)
  frameHi := (740572192163 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12578]
  agentFrame_pos := by norm_num only [agent12578]
  worldRadius := (2132295599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12578]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1621346783 / 1000000000000 : ℝ)
  lowerTail := (118892123 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (269617979 / 31250000000 : ℝ)
  ledger := by
    have h : (588720309 / 500000000000 : ℚ) +
        (604586271 / 62500000000000000 : ℚ) / (2132295599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1621346783 / 1000000000000 : ℚ) + (118892123 / 62500000000 : ℚ) ≤
        (269617979 / 31250000000 : ℚ) := by norm_num only
    have hc : (((588720309 / 500000000000 : ℚ) +
        (604586271 / 62500000000000000 : ℚ) / (2132295599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1621346783 / 1000000000000 : ℚ) + (118892123 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((269617979 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12578]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12578 :
    2 * 160 < 12578 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999861 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12578 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12579 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12579. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12579 : WorldParameters where
  hiddenCharge := (588697789 / 500000000000 : ℝ)
  frame := (125463635191 / 200000000000 : ℝ)
  moment := (9671369919 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12579 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (185138862337 / 125000000000 : ℝ)
    root := (4289814043 / 500000000000 : ℝ) }

noncomputable def scalar12579 : ScalarCertificate 12579 world12579 agent12579 where
  dimensionLo := 12579
  dimensionHi := 12579
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2132648799 / 1000000000000 : ℝ)
  frameLo := (125463635191 / 200000000000 : ℝ)
  frameHi := (185138862337 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12579]
  agentFrame_pos := by norm_num only [agent12579]
  worldRadius := (2132648799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12579]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (25311853 / 15625000000 : ℝ)
  lowerTail := (1900760737 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4311841091 / 500000000000 : ℝ)
  ledger := by
    have h : (588697789 / 500000000000 : ℚ) +
        (9671369919 / 1000000000000000000 : ℚ) / (2132648799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (25311853 / 15625000000 : ℚ) + (1900760737 / 1000000000000 : ℚ) ≤
        (4311841091 / 500000000000 : ℚ) := by norm_num only
    have hc : (((588697789 / 500000000000 : ℚ) +
        (9671369919 / 1000000000000000000 : ℚ) / (2132648799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (25311853 / 15625000000 : ℚ) + (1900760737 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4311841091 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12579]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12579 :
    2 * 160 < 12579 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1099999877 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12579 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12580 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12580. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12580 : WorldParameters where
  hiddenCharge := (1177350551 / 1000000000000 : ℝ)
  frame := (627304060829 / 1000000000000 : ℝ)
  moment := (4834680043 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12580 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (740497332167 / 500000000000 : ℝ)
    root := (4289463417 / 500000000000 : ℝ) }

noncomputable def scalar12580 : ScalarCertificate 12580 world12580 agent12580 where
  dimensionLo := 12580
  dimensionHi := 12580
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2133112799 / 1000000000000 : ℝ)
  frameLo := (627304060829 / 1000000000000 : ℝ)
  frameHi := (740497332167 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12580]
  agentFrame_pos := by norm_num only [agent12580]
  worldRadius := (2133112799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12580]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1618277279 / 1000000000000 : ℝ)
  lowerTail := (1898872743 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4309350577 / 500000000000 : ℝ)
  ledger := by
    have h : (1177350551 / 1000000000000 : ℚ) +
        (4834680043 / 500000000000000000 : ℚ) / (2133112799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1618277279 / 1000000000000 : ℚ) + (1898872743 / 1000000000000 : ℚ) ≤
        (4309350577 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1177350551 / 1000000000000 : ℚ) +
        (4834680043 / 500000000000000000 : ℚ) / (2133112799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1618277279 / 1000000000000 : ℚ) + (1898872743 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4309350577 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12580]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12580 :
    2 * 160 < 12580 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998239 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12580 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12581 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12581. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12581 : WorldParameters where
  hiddenCharge := (235461107 / 200000000000 : ℝ)
  frame := (627289947993 / 1000000000000 : ℝ)
  moment := (9667350837 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12581 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (148096121651 / 100000000000 : ℝ)
    root := (8578225797 / 1000000000000 : ℝ) }

noncomputable def scalar12581 : ScalarCertificate 12581 world12581 agent12581 where
  dimensionLo := 12581
  dimensionHi := 12581
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2133465999 / 1000000000000 : ℝ)
  frameLo := (627289947993 / 1000000000000 : ℝ)
  frameHi := (148096121651 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12581]
  agentFrame_pos := by norm_num only [agent12581]
  worldRadius := (2133465999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12581]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (323378421 / 200000000000 : ℝ)
  lowerTail := (379472529 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8614615879 / 1000000000000 : ℝ)
  ledger := by
    have h : (235461107 / 200000000000 : ℚ) +
        (9667350837 / 1000000000000000000 : ℚ) / (2133465999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (323378421 / 200000000000 : ℚ) + (379472529 / 200000000000 : ℚ) ≤
        (8614615879 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((235461107 / 200000000000 : ℚ) +
        (9667350837 / 1000000000000000000 : ℚ) / (2133465999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (323378421 / 200000000000 : ℚ) + (379472529 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8614615879 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12581]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12581 :
    2 * 160 < 12581 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999457 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12581 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12582 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12582. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12582 : WorldParameters where
  hiddenCharge := (294315133 / 250000000000 : ℝ)
  frame := (78409479681 / 125000000000 : ℝ)
  moment := (9665342171 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12582 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (46278993439 / 31250000000 : ℝ)
    root := (343100999 / 40000000000 : ℝ) }

noncomputable def scalar12582 : ScalarCertificate 12582 world12582 agent12582 where
  dimensionLo := 12582
  dimensionHi := 12582
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2133819299 / 1000000000000 : ℝ)
  frameLo := (78409479681 / 125000000000 : ℝ)
  frameHi := (46278993439 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12582]
  agentFrame_pos := by norm_num only [agent12582]
  worldRadius := (2133819299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12582]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (403877103 / 250000000000 : ℝ)
  lowerTail := (1895854077 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8610534197 / 1000000000000 : ℝ)
  ledger := by
    have h : (294315133 / 250000000000 : ℚ) +
        (9665342171 / 1000000000000000000 : ℚ) / (2133819299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (403877103 / 250000000000 : ℚ) + (1895854077 / 1000000000000 : ℚ) ≤
        (8610534197 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((294315133 / 250000000000 : ℚ) +
        (9665342171 / 1000000000000000000 : ℚ) / (2133819299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (403877103 / 250000000000 : ℚ) + (1895854077 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8610534197 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12582]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12582 :
    2 * 160 < 12582 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999169 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12582 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12583 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12583. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12583 : WorldParameters where
  hiddenCharge := (58860777 / 50000000000 : ℝ)
  frame := (627261729193 / 1000000000000 : ℝ)
  moment := (1207916761 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12583 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (740447189497 / 500000000000 : ℝ)
    root := (85768243 / 10000000000 : ℝ) }

noncomputable def scalar12583 : ScalarCertificate 12583 world12583 agent12583 where
  dimensionLo := 12583
  dimensionHi := 12583
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2134172599 / 1000000000000 : ℝ)
  frameLo := (627261729193 / 1000000000000 : ℝ)
  frameHi := (740447189497 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12583]
  agentFrame_pos := by norm_num only [agent12583]
  worldRadius := (2134172599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12583]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1614126007 / 1000000000000 : ℝ)
  lowerTail := (1894346833 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8606455911 / 1000000000000 : ℝ)
  ledger := by
    have h : (58860777 / 50000000000 : ℚ) +
        (1207916761 / 125000000000000000 : ℚ) / (2134172599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1614126007 / 1000000000000 : ℚ) + (1894346833 / 1000000000000 : ℚ) ≤
        (8606455911 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((58860777 / 50000000000 : ℚ) +
        (1207916761 / 125000000000000000 : ℚ) / (2134172599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1614126007 / 1000000000000 : ℚ) + (1894346833 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8606455911 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12583]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12583 :
    2 * 160 < 12583 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999121 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12583 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12584 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12584. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12584 : WorldParameters where
  hiddenCharge := (1177170561 / 1000000000000 : ℝ)
  frame := (627247623227 / 1000000000000 : ℝ)
  moment := (2415331647 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12584 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (9255381183 / 6250000000 : ℝ)
    root := (8576123907 / 1000000000000 : ℝ) }

noncomputable def scalar12584 : ScalarCertificate 12584 world12584 agent12584 where
  dimensionLo := 12584
  dimensionHi := 12584
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2134525899 / 1000000000000 : ℝ)
  frameLo := (627247623227 / 1000000000000 : ℝ)
  frameHi := (9255381183 / 6250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12584]
  agentFrame_pos := by norm_num only [agent12584]
  worldRadius := (2134525899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12584]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1612745049 / 1000000000000 : ℝ)
  lowerTail := (946420539 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (430119067 / 50000000000 : ℝ)
  ledger := by
    have h : (1177170561 / 1000000000000 : ℚ) +
        (2415331647 / 250000000000000000 : ℚ) / (2134525899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1612745049 / 1000000000000 : ℚ) + (946420539 / 500000000000 : ℚ) ≤
        (430119067 / 50000000000 : ℚ) := by norm_num only
    have hc : (((1177170561 / 1000000000000 : ℚ) +
        (2415331647 / 250000000000000000 : ℚ) / (2134525899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1612745049 / 1000000000000 : ℚ) + (946420539 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((430119067 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12584]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12584 :
    2 * 160 < 12584 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999803 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12584 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12585 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12585. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12585 : WorldParameters where
  hiddenCharge := (1177125593 / 1000000000000 : ℝ)
  frame := (627233519549 / 1000000000000 : ℝ)
  moment := (965931967 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12585 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (296165524179 / 200000000000 : ℝ)
    root := (857542373 / 100000000000 : ℝ) }

noncomputable def scalar12585 : ScalarCertificate 12585 world12585 agent12585 where
  dimensionLo := 12585
  dimensionHi := 12585
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2134879099 / 1000000000000 : ℝ)
  frameLo := (627233519549 / 1000000000000 : ℝ)
  frameHi := (296165524179 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12585]
  agentFrame_pos := by norm_num only [agent12585]
  worldRadius := (2134879099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12585]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (12890923 / 8000000000 : ℝ)
  lowerTail := (1891336641 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8598310349 / 1000000000000 : ℝ)
  ledger := by
    have h : (1177125593 / 1000000000000 : ℚ) +
        (965931967 / 100000000000000000 : ℚ) / (2134879099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (12890923 / 8000000000 : ℚ) + (1891336641 / 1000000000000 : ℚ) ≤
        (8598310349 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1177125593 / 1000000000000 : ℚ) +
        (965931967 / 100000000000000000 : ℚ) / (2134879099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (12890923 / 8000000000 : ℚ) + (1891336641 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8598310349 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12585]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12585 :
    2 * 160 < 12585 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999083 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12585 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12586 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12586. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12586 : WorldParameters where
  hiddenCharge := (588540319 / 500000000000 : ℝ)
  frame := (627219418159 / 1000000000000 : ℝ)
  moment := (1207164167 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12586 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (296158853577 / 200000000000 : ℝ)
    root := (1071840471 / 125000000000 : ℝ) }

noncomputable def scalar12586 : ScalarCertificate 12586 world12586 agent12586 where
  dimensionLo := 12586
  dimensionHi := 12586
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2135232499 / 1000000000000 : ℝ)
  frameLo := (627219418159 / 1000000000000 : ℝ)
  frameHi := (296158853577 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12586]
  agentFrame_pos := by norm_num only [agent12586]
  worldRadius := (2135232499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12586]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1609987241 / 1000000000000 : ℝ)
  lowerTail := (472458449 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8594242873 / 1000000000000 : ℝ)
  ledger := by
    have h : (588540319 / 500000000000 : ℚ) +
        (1207164167 / 125000000000000000 : ℚ) / (2135232499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1609987241 / 1000000000000 : ℚ) + (472458449 / 250000000000 : ℚ) ≤
        (8594242873 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((588540319 / 500000000000 : ℚ) +
        (1207164167 / 125000000000000000 : ℚ) / (2135232499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1609987241 / 1000000000000 : ℚ) + (472458449 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8594242873 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12586]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12586 :
    2 * 160 < 12586 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999647 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12586 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12587 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12587. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12587 : WorldParameters where
  hiddenCharge := (235407139 / 200000000000 : ℝ)
  frame := (39200332441 / 62500000000 : ℝ)
  moment := (9655307583 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12587 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1480760936181 / 1000000000000 : ℝ)
    root := (66984531 / 7812500000 : ℝ) }

noncomputable def scalar12587 : ScalarCertificate 12587 world12587 agent12587 where
  dimensionLo := 12587
  dimensionHi := 12587
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2135586799 / 1000000000000 : ℝ)
  frameLo := (39200332441 / 62500000000 : ℝ)
  frameHi := (1480760936181 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12587]
  agentFrame_pos := by norm_num only [agent12587]
  worldRadius := (2135586799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12587]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1608607533 / 1000000000000 : ℝ)
  lowerTail := (118020593 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2147542839 / 250000000000 : ℝ)
  ledger := by
    have h : (235407139 / 200000000000 : ℚ) +
        (9655307583 / 1000000000000000000 : ℚ) / (2135586799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1608607533 / 1000000000000 : ℚ) + (118020593 / 62500000000 : ℚ) ≤
        (2147542839 / 250000000000 : ℚ) := by norm_num only
    have hc : (((235407139 / 200000000000 : ℚ) +
        (9655307583 / 1000000000000000000 : ℚ) / (2135586799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1608607533 / 1000000000000 : ℚ) + (118020593 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((2147542839 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12587]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12587 :
    2 * 160 < 12587 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997697 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12587 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12588 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12588. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12588 : WorldParameters where
  hiddenCharge := (1176990763 / 1000000000000 : ℝ)
  frame := (627191222241 / 1000000000000 : ℝ)
  moment := (2413325603 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12588 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (148072761983 / 100000000000 : ℝ)
    root := (8573312647 / 1000000000000 : ℝ) }

noncomputable def scalar12588 : ScalarCertificate 12588 world12588 agent12588 where
  dimensionLo := 12588
  dimensionHi := 12588
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2135942099 / 1000000000000 : ℝ)
  frameLo := (627191222241 / 1000000000000 : ℝ)
  frameHi := (148072761983 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12588]
  agentFrame_pos := by norm_num only [agent12588]
  worldRadius := (2135942099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12588]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1607226619 / 1000000000000 : ℝ)
  lowerTail := (377364817 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8586096337 / 1000000000000 : ℝ)
  ledger := by
    have h : (1176990763 / 1000000000000 : ℚ) +
        (2413325603 / 250000000000000000 : ℚ) / (2135942099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1607226619 / 1000000000000 : ℚ) + (377364817 / 200000000000 : ℚ) ≤
        (8586096337 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1176990763 / 1000000000000 : ℚ) +
        (2413325603 / 250000000000000000 : ℚ) / (2135942099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1607226619 / 1000000000000 : ℚ) + (377364817 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8586096337 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12588]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12588 :
    2 * 160 < 12588 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999997093 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12588 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12589 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12589. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12589 : WorldParameters where
  hiddenCharge := (294236461 / 250000000000 : ℝ)
  frame := (627177127711 / 1000000000000 : ℝ)
  moment := (301603057 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12589 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (370173581191 / 250000000000 : ℝ)
    root := (2143151389 / 250000000000 : ℝ) }

noncomputable def scalar12589 : ScalarCertificate 12589 world12589 agent12589 where
  dimensionLo := 12589
  dimensionHi := 12589
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2136297399 / 1000000000000 : ℝ)
  frameLo := (627177127711 / 1000000000000 : ℝ)
  frameHi := (370173581191 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12589]
  agentFrame_pos := by norm_num only [agent12589]
  worldRadius := (2136297399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12589]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (802923551 / 500000000000 : ℝ)
  lowerTail := (1885320121 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1072753117 / 125000000000 : ℝ)
  ledger := by
    have h : (294236461 / 250000000000 : ℚ) +
        (301603057 / 31250000000000000 : ℚ) / (2136297399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (802923551 / 500000000000 : ℚ) + (1885320121 / 1000000000000 : ℚ) ≤
        (1072753117 / 125000000000 : ℚ) := by norm_num only
    have hc : (((294236461 / 250000000000 : ℚ) +
        (301603057 / 31250000000000000 : ℚ) / (2136297399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (802923551 / 500000000000 : ℚ) + (1885320121 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1072753117 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12589]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12589 :
    2 * 160 < 12589 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996117 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12589 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12590 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12590. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12590 : WorldParameters where
  hiddenCharge := (1176900937 / 1000000000000 : ℝ)
  frame := (627163035467 / 1000000000000 : ℝ)
  moment := (1206161727 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12590 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1480578395741 / 1000000000000 : ℝ)
    root := (4285949313 / 500000000000 : ℝ) }

noncomputable def scalar12590 : ScalarCertificate 12590 world12590 agent12590 where
  dimensionLo := 12590
  dimensionHi := 12590
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2136763599 / 1000000000000 : ℝ)
  frameLo := (627163035467 / 1000000000000 : ℝ)
  frameHi := (1480578395741 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12590]
  agentFrame_pos := by norm_num only [agent12590]
  worldRadius := (2136763599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12590]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (401044259 / 250000000000 : ℝ)
  lowerTail := (941722239 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4288536349 / 500000000000 : ℝ)
  ledger := by
    have h : (1176900937 / 1000000000000 : ℚ) +
        (1206161727 / 125000000000000000 : ℚ) / (2136763599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (401044259 / 250000000000 : ℚ) + (941722239 / 500000000000 : ℚ) ≤
        (4288536349 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1176900937 / 1000000000000 : ℚ) +
        (1206161727 / 125000000000000000 : ℚ) / (2136763599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (401044259 / 250000000000 : ℚ) + (941722239 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4288536349 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12590]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12590 :
    2 * 160 < 12590 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998579 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12590 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12591 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12591. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12591 : WorldParameters where
  hiddenCharge := (1176856041 / 1000000000000 : ℝ)
  frame := (156787236377 / 250000000000 : ℝ)
  moment := (9647290391 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12591 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1480545138249 / 1000000000000 : ℝ)
    root := (4285595997 / 500000000000 : ℝ) }

noncomputable def scalar12591 : ScalarCertificate 12591 world12591 agent12591 where
  dimensionLo := 12591
  dimensionHi := 12591
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2137118899 / 1000000000000 : ℝ)
  frameLo := (156787236377 / 250000000000 : ℝ)
  frameHi := (1480545138249 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12591]
  agentFrame_pos := by norm_num only [agent12591]
  worldRadius := (2137118899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12591]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1602800483 / 1000000000000 : ℝ)
  lowerTail := (235242949 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (428650453 / 50000000000 : ℝ)
  ledger := by
    have h : (1176856041 / 1000000000000 : ℚ) +
        (9647290391 / 1000000000000000000 : ℚ) / (2137118899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1602800483 / 1000000000000 : ℚ) + (235242949 / 125000000000 : ℚ) ≤
        (428650453 / 50000000000 : ℚ) := by norm_num only
    have hc : (((1176856041 / 1000000000000 : ℚ) +
        (9647290391 / 1000000000000000000 : ℚ) / (2137118899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1602800483 / 1000000000000 : ℚ) + (235242949 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((428650453 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12591]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12591 :
    2 * 160 < 12591 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998317 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12591 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12592 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12592. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12592 : WorldParameters where
  hiddenCharge := (588405579 / 500000000000 : ℝ)
  frame := (627134857833 / 1000000000000 : ℝ)
  moment := (4822643773 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12592 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1480511902007 / 1000000000000 : ℝ)
    root := (1071310699 / 125000000000 : ℝ) }

noncomputable def scalar12592 : ScalarCertificate 12592 world12592 agent12592 where
  dimensionLo := 12592
  dimensionHi := 12592
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2137474299 / 1000000000000 : ℝ)
  frameLo := (627134857833 / 1000000000000 : ℝ)
  frameHi := (1480511902007 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12592]
  agentFrame_pos := by norm_num only [agent12592]
  worldRadius := (2137474299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12592]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (320285083 / 200000000000 : ℝ)
  lowerTail := (1880444241 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4284474513 / 500000000000 : ℝ)
  ledger := by
    have h : (588405579 / 500000000000 : ℚ) +
        (4822643773 / 500000000000000000 : ℚ) / (2137474299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (320285083 / 200000000000 : ℚ) + (1880444241 / 1000000000000 : ℚ) ≤
        (4284474513 / 500000000000 : ℚ) := by norm_num only
    have hc : (((588405579 / 500000000000 : ℚ) +
        (4822643773 / 500000000000000000 : ℚ) / (2137474299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (320285083 / 200000000000 : ℚ) + (1880444241 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4284474513 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12592]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12592 :
    2 * 160 < 12592 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999061 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12592 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12593 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12593. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12593 : WorldParameters where
  hiddenCharge := (588383143 / 500000000000 : ℝ)
  frame := (313560386221 / 500000000000 : ℝ)
  moment := (9643285283 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12593 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (740239340531 / 500000000000 : ℝ)
    root := (171395587 / 20000000000 : ℝ) }

noncomputable def scalar12593 : ScalarCertificate 12593 world12593 agent12593 where
  dimensionLo := 12593
  dimensionHi := 12593
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2137829599 / 1000000000000 : ℝ)
  frameLo := (313560386221 / 500000000000 : ℝ)
  frameHi := (740239340531 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12593]
  agentFrame_pos := by norm_num only [agent12593]
  worldRadius := (2137829599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12593]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (32001031 / 20000000000 : ℝ)
  lowerTail := (1878946119 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (21412231 / 2500000000 : ℝ)
  ledger := by
    have h : (588383143 / 500000000000 : ℚ) +
        (9643285283 / 1000000000000000000 : ℚ) / (2137829599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (32001031 / 20000000000 : ℚ) + (1878946119 / 1000000000000 : ℚ) ≤
        (21412231 / 2500000000 : ℚ) := by norm_num only
    have hc : (((588383143 / 500000000000 : ℚ) +
        (9643285283 / 1000000000000000000 : ℚ) / (2137829599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (32001031 / 20000000000 : ℚ) + (1878946119 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((21412231 / 2500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12593]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12593 :
    2 * 160 < 12593 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999995663 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12593 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12594 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12594. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12594 : WorldParameters where
  hiddenCharge := (1176721427 / 1000000000000 : ℝ)
  frame := (313553344667 / 500000000000 : ℝ)
  moment := (24103209 / 2500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12594 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (296089095081 / 200000000000 : ℝ)
    root := (1713814681 / 200000000000 : ℝ) }

noncomputable def scalar12594 : ScalarCertificate 12594 world12594 agent12594 where
  dimensionLo := 12594
  dimensionHi := 12594
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2138184899 / 1000000000000 : ℝ)
  frameLo := (313553344667 / 500000000000 : ℝ)
  frameHi := (296089095081 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12594]
  agentFrame_pos := by norm_num only [agent12594]
  worldRadius := (2138184899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12594]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (399669777 / 250000000000 : ℝ)
  lowerTail := (375489891 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8560839437 / 1000000000000 : ℝ)
  ledger := by
    have h : (1176721427 / 1000000000000 : ℚ) +
        (24103209 / 2500000000000000 : ℚ) / (2138184899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (399669777 / 250000000000 : ℚ) + (375489891 / 200000000000 : ℚ) ≤
        (8560839437 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1176721427 / 1000000000000 : ℚ) +
        (24103209 / 2500000000000000 : ℚ) / (2138184899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (399669777 / 250000000000 : ℚ) + (375489891 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8560839437 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12594]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12594 :
    2 * 160 < 12594 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999921 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12594 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12595 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12595. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12595 : WorldParameters where
  hiddenCharge := (58833829 / 50000000000 : ℝ)
  frame := (627092608509 / 1000000000000 : ℝ)
  moment := (9639282497 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12595 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1480412249377 / 1000000000000 : ℝ)
    root := (856836769 / 100000000000 : ℝ) }

noncomputable def scalar12595 : ScalarCertificate 12595 world12595 agent12595 where
  dimensionLo := 12595
  dimensionHi := 12595
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2138540399 / 1000000000000 : ℝ)
  frameLo := (627092608509 / 1000000000000 : ℝ)
  frameHi := (1480412249377 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12595]
  agentFrame_pos := by norm_num only [agent12595]
  worldRadius := (2138540399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12595]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1597308041 / 1000000000000 : ℝ)
  lowerTail := (93797709 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1069598703 / 125000000000 : ℝ)
  ledger := by
    have h : (58833829 / 50000000000 : ℚ) +
        (9639282497 / 1000000000000000000 : ℚ) / (2138540399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1597308041 / 1000000000000 : ℚ) + (93797709 / 50000000000 : ℚ) ≤
        (1069598703 / 125000000000 : ℚ) := by norm_num only
    have hc : (((58833829 / 50000000000 : ℚ) +
        (9639282497 / 1000000000000000000 : ℚ) / (2138540399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1597308041 / 1000000000000 : ℚ) + (93797709 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1069598703 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12595]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12595 :
    2 * 160 < 12595 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999999051 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12595 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12596 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12596. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12596 : WorldParameters where
  hiddenCharge := (18384871 / 15625000000 : ℝ)
  frame := (313539264983 / 500000000000 : ℝ)
  moment := (385491279 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12596 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (740189379701 / 500000000000 : ℝ)
    root := (4283831067 / 500000000000 : ℝ) }

noncomputable def scalar12596 : ScalarCertificate 12596 world12596 agent12596 where
  dimensionLo := 12596
  dimensionHi := 12596
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2138896199 / 1000000000000 : ℝ)
  frameLo := (313539264983 / 500000000000 : ℝ)
  frameHi := (740189379701 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12596]
  agentFrame_pos := by norm_num only [agent12596]
  worldRadius := (2138896199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12596]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (319187443 / 200000000000 : ℝ)
  lowerTail := (1874458901 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1710548047 / 200000000000 : ℝ)
  ledger := by
    have h : (18384871 / 15625000000 : ℚ) +
        (385491279 / 40000000000000000 : ℚ) / (2138896199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (319187443 / 200000000000 : ℚ) + (1874458901 / 1000000000000 : ℚ) ≤
        (1710548047 / 200000000000 : ℚ) := by norm_num only
    have hc : (((18384871 / 15625000000 : ℚ) +
        (385491279 / 40000000000000000 : ℚ) / (2138896199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (319187443 / 200000000000 : ℚ) + (1874458901 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1710548047 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12596]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12596 :
    2 * 160 < 12596 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999993941 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12596 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12597 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12597. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12597 : WorldParameters where
  hiddenCharge := (1176586921 / 1000000000000 : ℝ)
  frame := (78383056713 / 125000000000 : ℝ)
  moment := (9635282033 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12597 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1480345278763 / 1000000000000 : ℝ)
    root := (2141739219 / 250000000000 : ℝ) }

noncomputable def scalar12597 : ScalarCertificate 12597 world12597 agent12597 where
  dimensionLo := 12597
  dimensionHi := 12597
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2139251999 / 1000000000000 : ℝ)
  frameLo := (78383056713 / 125000000000 : ℝ)
  frameHi := (1480345278763 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12597]
  agentFrame_pos := by norm_num only [agent12597]
  worldRadius := (2139251999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12597]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1594567781 / 1000000000000 : ℝ)
  lowerTail := (1872965043 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8548694437 / 1000000000000 : ℝ)
  ledger := by
    have h : (1176586921 / 1000000000000 : ℚ) +
        (9635282033 / 1000000000000000000 : ℚ) / (2139251999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1594567781 / 1000000000000 : ℚ) + (1872965043 / 1000000000000 : ℚ) ≤
        (8548694437 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1176586921 / 1000000000000 : ℚ) +
        (9635282033 / 1000000000000000000 : ℚ) / (2139251999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1594567781 / 1000000000000 : ℚ) + (1872965043 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8548694437 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12597]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12597 :
    2 * 160 < 12597 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999839 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12597 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12598 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12598. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12598 : WorldParameters where
  hiddenCharge := (1176542109 / 1000000000000 : ℝ)
  frame := (627050379723 / 1000000000000 : ℝ)
  moment := (9633282671 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12598 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1480311825271 / 1000000000000 : ℝ)
    root := (4283125923 / 500000000000 : ℝ) }

noncomputable def scalar12598 : ScalarCertificate 12598 world12598 agent12598 where
  dimensionLo := 12598
  dimensionHi := 12598
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2139607799 / 1000000000000 : ℝ)
  frameLo := (627050379723 / 1000000000000 : ℝ)
  frameHi := (1480311825271 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12598]
  agentFrame_pos := by norm_num only [agent12598]
  worldRadius := (2139607799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12598]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1593199757 / 1000000000000 : ℝ)
  lowerTail := (467868161 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8344387 / 976562500 : ℝ)
  ledger := by
    have h : (1176542109 / 1000000000000 : ℚ) +
        (9633282671 / 1000000000000000000 : ℚ) / (2139607799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1593199757 / 1000000000000 : ℚ) + (467868161 / 250000000000 : ℚ) ≤
        (8344387 / 976562500 : ℚ) := by norm_num only
    have hc : (((1176542109 / 1000000000000 : ℚ) +
        (9633282671 / 1000000000000000000 : ℚ) / (2139607799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1593199757 / 1000000000000 : ℚ) + (467868161 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8344387 / 976562500 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12598]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12598 :
    2 * 160 < 12598 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996573 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12598 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12599 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12599. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12599 : WorldParameters where
  hiddenCharge := (1176497309 / 1000000000000 : ℝ)
  frame := (313518154011 / 500000000000 : ℝ)
  moment := (9631283889 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12599 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (740139193517 / 500000000000 : ℝ)
    root := (267673343 / 31250000000 : ℝ) }

noncomputable def scalar12599 : ScalarCertificate 12599 world12599 agent12599 where
  dimensionLo := 12599
  dimensionHi := 12599
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2139963599 / 1000000000000 : ℝ)
  frameLo := (313518154011 / 500000000000 : ℝ)
  frameHi := (740139193517 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12599]
  agentFrame_pos := by norm_num only [agent12599]
  worldRadius := (2139963599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12599]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1591833023 / 1000000000000 : ℝ)
  lowerTail := (186998157 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2135153383 / 250000000000 : ℝ)
  ledger := by
    have h : (1176497309 / 1000000000000 : ℚ) +
        (9631283889 / 1000000000000000000 : ℚ) / (2139963599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1591833023 / 1000000000000 : ℚ) + (186998157 / 100000000000 : ℚ) ≤
        (2135153383 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1176497309 / 1000000000000 : ℚ) +
        (9631283889 / 1000000000000000000 : ℚ) / (2139963599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1591833023 / 1000000000000 : ℚ) + (186998157 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2135153383 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12599]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12599 :
    2 * 160 < 12599 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998193 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12599 {← IO.monoMsNow}" : IO Unit)
