import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 12224 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12224. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12224 : WorldParameters where
  hiddenCharge := (149271739 / 125000000000 : ℝ)
  frame := (79059801537 / 125000000000 : ℝ)
  moment := (5211720093 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12224 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (187102386507 / 125000000000 : ℝ)
    root := (7448892351 / 1000000000000 : ℝ) }

noncomputable def scalar12224 : ScalarCertificate 12224 world12224 agent12224 where
  dimensionLo := 12224
  dimensionHi := 12224
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2359369999 / 1000000000000 : ℝ)
  frameLo := (79059801537 / 125000000000 : ℝ)
  frameHi := (187102386507 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12224]
  agentFrame_pos := by norm_num only [agent12224]
  worldRadius := (2359369999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12224]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (246223039 / 200000000000 : ℝ)
  lowerTail := (392279847 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3833021093 / 500000000000 : ℝ)
  ledger := by
    have h : (149271739 / 125000000000 : ℚ) +
        (5211720093 / 500000000000000000 : ℚ) / (2359369999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (246223039 / 200000000000 : ℚ) + (392279847 / 250000000000 : ℚ) ≤
        (3833021093 / 500000000000 : ℚ) := by norm_num only
    have hc : (((149271739 / 125000000000 : ℚ) +
        (5211720093 / 500000000000000000 : ℚ) / (2359369999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (246223039 / 200000000000 : ℚ) + (392279847 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3833021093 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12224]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12224 :
    2 * 160 < 12224 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (687499943 / 62500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12224 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11883 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11883. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11883 : WorldParameters where
  hiddenCharge := (1211911361 / 1000000000000 : ℝ)
  frame := (127546730133 / 200000000000 : ℝ)
  moment := (560633139 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11883 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (184373615191 / 125000000000 : ℝ)
    root := (7286302449 / 1000000000000 : ℝ) }

noncomputable def scalar11883 : ScalarCertificate 11883 world11883 agent11883 where
  dimensionLo := 11883
  dimensionHi := 11883
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2382397599 / 1000000000000 : ℝ)
  frameLo := (127546730133 / 200000000000 : ℝ)
  frameHi := (184373615191 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11883]
  agentFrame_pos := by norm_num only [agent11883]
  worldRadius := (2382397599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11883]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (652171123 / 500000000000 : ℝ)
  lowerTail := (332822141 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7955158893 / 1000000000000 : ℝ)
  ledger := by
    have h : (1211911361 / 1000000000000 : ℚ) +
        (560633139 / 50000000000000000 : ℚ) / (2382397599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (652171123 / 500000000000 : ℚ) + (332822141 / 200000000000 : ℚ) ≤
        (7955158893 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1211911361 / 1000000000000 : ℚ) +
        (560633139 / 50000000000000000 : ℚ) / (2382397599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (652171123 / 500000000000 : ℚ) + (332822141 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7955158893 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11883]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11883 :
    2 * 160 < 11883 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999591 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11883 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding11883 :
    (1211911360169504030683 / 1000000000000000000000000 : ℝ) ≤ world11883.hiddenCharge ∧
    (79716706333027400867551 / 125000000000000000000000 : ℝ) ≤ world11883.frame ∧
    (560633139 / 50000000000000000 : ℝ) ≤ world11883.moment ∧
    (1474988921527989729980779 / 1000000000000000000000000 : ℝ) ≤ agent11883.frame ∧
    (7286302448575946721653 / 1000000000000000000000000 : ℝ) ≤ agent11883.root ∧
    scalar11883.worldRadius ≤ (2382397599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (40252594400440858709 / 31250000000000000000000 : ℝ) ≤ agent11883.charge ∧
    (652171122645246930889 / 500000000000000000000000 : ℝ) ≤ scalar11883.upperTail ∧
    (1664110704781438215011 / 1000000000000000000000000 : ℝ) ≤ scalar11883.lowerTail ∧
    scalar11883.totalBudget ≤ (3977579446916187422991 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11883, agent11883, scalar11883] <;> simp only [true_and]

theorem source_rounding12224 :
    (1194173911267700431443 / 1000000000000000000000000 : ℝ) ≤ world12224.hiddenCharge ∧
    (316239206147686323222821 / 500000000000000000000000 : ℝ) ≤ world12224.frame ∧
    (5211720092617493 / 500000000000000000000000 : ℝ) ≤ world12224.moment ∧
    (748409546027764714802737 / 500000000000000000000000 : ℝ) ≤ agent12224.frame ∧
    (931111543837130899493 / 125000000000000000000000 : ℝ) ≤ agent12224.root ∧
    scalar12224.worldRadius ≤ (2359369999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (250379369471560156451 / 200000000000000000000000 : ℝ) ≤ agent12224.charge ∧
    (307778798583445430979 / 250000000000000000000000 : ℝ) ≤ scalar12224.upperTail ∧
    (1569119387555760332211 / 1000000000000000000000000 : ℝ) ≤ scalar12224.lowerTail ∧
    scalar12224.totalBudget ≤ (7666042186481961131663 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12224, agent12224, scalar12224] <;> simp only [true_and]

noncomputable def paperAgent11883 : AgentParameters :=
  { agent11883 with charge := (80505189 / 62500000000 : ℝ) }

theorem agent_is_repriced11883 : agent11883 =
    BstLean.Part265.agentRepriced 11883 world11883 paperAgent11883 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11883, agent11883]

noncomputable def paperAgent12224 : AgentParameters :=
  { agent12224 with charge := (1251896851 / 1000000000000 : ℝ) }

theorem agent_is_repriced12224 : agent12224 =
    BstLean.Part265.agentRepriced 12224 world12224 paperAgent12224 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12224, agent12224]

end BstLean.Part281
