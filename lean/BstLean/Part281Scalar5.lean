import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 11984 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11984. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11984 : WorldParameters where
  hiddenCharge := (1206480051 / 1000000000000 : ℝ)
  frame := (636144969477 / 1000000000000 : ℝ)
  moment := (5483357969 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11984 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470399031461 / 1000000000000 : ℝ)
    root := (7218430453 / 1000000000000 : ℝ) }

noncomputable def scalar11984 : ScalarCertificate 11984 world11984 agent11984 where
  dimensionLo := 11984
  dimensionHi := 11984
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2424261699 / 1000000000000 : ℝ)
  frameLo := (636144969477 / 1000000000000 : ℝ)
  frameHi := (1470399031461 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11984]
  agentFrame_pos := by norm_num only [agent11984]
  worldRadius := (2424261699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11984]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1190991953 / 1000000000000 : ℝ)
  lowerTail := (152985393 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (949077979 / 125000000000 : ℝ)
  ledger := by
    have h : (1206480051 / 1000000000000 : ℚ) +
        (5483357969 / 500000000000000000 : ℚ) / (2424261699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1190991953 / 1000000000000 : ℚ) + (152985393 / 100000000000 : ℚ) ≤
        (949077979 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1206480051 / 1000000000000 : ℚ) +
        (5483357969 / 500000000000000000 : ℚ) / (2424261699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1190991953 / 1000000000000 : ℚ) + (152985393 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((949077979 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11984]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11984 :
    2 * 160 < 11984 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999591 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11984 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11985 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11985. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11985 : WorldParameters where
  hiddenCharge := (603213523 / 500000000000 : ℝ)
  frame := (318064689089 / 500000000000 : ℝ)
  moment := (10964318663 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11985 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470354362067 / 1000000000000 : ℝ)
    root := (7217770261 / 1000000000000 : ℝ) }

noncomputable def scalar11985 : ScalarCertificate 11985 world11985 agent11985 where
  dimensionLo := 11985
  dimensionHi := 11985
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2424676699 / 1000000000000 : ℝ)
  frameLo := (318064689089 / 500000000000 : ℝ)
  frameHi := (1470354362067 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11985]
  agentFrame_pos := by norm_num only [agent11985]
  worldRadius := (2424676699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11985]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1189927657 / 1000000000000 : ℝ)
  lowerTail := (1528588967 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (379459751 / 50000000000 : ℝ)
  ledger := by
    have h : (603213523 / 500000000000 : ℚ) +
        (10964318663 / 1000000000000000000 : ℚ) / (2424676699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1189927657 / 1000000000000 : ℚ) + (1528588967 / 1000000000000 : ℚ) ≤
        (379459751 / 50000000000 : ℚ) := by norm_num only
    have hc : (((603213523 / 500000000000 : ℚ) +
        (10964318663 / 1000000000000000000 : ℚ) / (2424676699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1189927657 / 1000000000000 : ℚ) + (1528588967 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((379459751 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11985]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11985 :
    2 * 160 < 11985 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996499 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11985 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11986 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11986. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11986 : WorldParameters where
  hiddenCharge := (241274811 / 200000000000 : ℝ)
  frame := (636113789563 / 1000000000000 : ℝ)
  moment := (10961922119 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11986 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470309710401 / 1000000000000 : ℝ)
    root := (57736883 / 8000000000 : ℝ) }

noncomputable def scalar11986 : ScalarCertificate 11986 world11986 agent11986 where
  dimensionLo := 11986
  dimensionHi := 11986
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2425091899 / 1000000000000 : ℝ)
  frameLo := (636113789563 / 1000000000000 : ℝ)
  frameHi := (1470309710401 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11986]
  agentFrame_pos := by norm_num only [agent11986]
  worldRadius := (2425091899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11986]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1188864653 / 1000000000000 : ℝ)
  lowerTail := (30546509 / 20000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3792884691 / 500000000000 : ℝ)
  ledger := by
    have h : (241274811 / 200000000000 : ℚ) +
        (10961922119 / 1000000000000000000 : ℚ) / (2425091899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1188864653 / 1000000000000 : ℚ) + (30546509 / 20000000000 : ℚ) ≤
        (3792884691 / 500000000000 : ℚ) := by norm_num only
    have hc : (((241274811 / 200000000000 : ℚ) +
        (10961922119 / 1000000000000000000 : ℚ) / (2425091899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1188864653 / 1000000000000 : ℚ) + (30546509 / 20000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3792884691 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11986]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11986 :
    2 * 160 < 11986 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998669 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11986 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11987 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11987. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11987 : WorldParameters where
  hiddenCharge := (1206321079 / 1000000000000 : ℝ)
  frame := (39756137727 / 62500000000 : ℝ)
  moment := (2739881577 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11987 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470265088343 / 1000000000000 : ℝ)
    root := (7216450717 / 1000000000000 : ℝ) }

noncomputable def scalar11987 : ScalarCertificate 11987 world11987 agent11987 where
  dimensionLo := 11987
  dimensionHi := 11987
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2425506999 / 1000000000000 : ℝ)
  frameLo := (39756137727 / 62500000000 : ℝ)
  frameHi := (1470265088343 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11987]
  agentFrame_pos := by norm_num only [agent11987]
  worldRadius := (2425506999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11987]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1187802717 / 1000000000000 : ℝ)
  lowerTail := (1526063127 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1895586727 / 250000000000 : ℝ)
  ledger := by
    have h : (1206321079 / 1000000000000 : ℚ) +
        (2739881577 / 250000000000000000 : ℚ) / (2425506999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1187802717 / 1000000000000 : ℚ) + (1526063127 / 1000000000000 : ℚ) ≤
        (1895586727 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1206321079 / 1000000000000 : ℚ) +
        (2739881577 / 250000000000000000 : ℚ) / (2425506999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1187802717 / 1000000000000 : ℚ) + (1526063127 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1895586727 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11987]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11987 :
    2 * 160 < 11987 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997141 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11987 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11988 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11988. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11988 : WorldParameters where
  hiddenCharge := (603134059 / 500000000000 : ℝ)
  frame := (19877581887 / 31250000000 : ℝ)
  moment := (10957131227 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11988 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470220483987 / 1000000000000 : ℝ)
    root := (7215791287 / 1000000000000 : ℝ) }

noncomputable def scalar11988 : ScalarCertificate 11988 world11988 agent11988 where
  dimensionLo := 11988
  dimensionHi := 11988
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2425922099 / 1000000000000 : ℝ)
  frameLo := (19877581887 / 31250000000 : ℝ)
  frameHi := (1470220483987 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11988]
  agentFrame_pos := by norm_num only [agent11988]
  worldRadius := (2425922099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11988]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1898787 / 1600000000 : ℝ)
  lowerTail := (762401011 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (757892749 / 100000000000 : ℝ)
  ledger := by
    have h : (603134059 / 500000000000 : ℚ) +
        (10957131227 / 1000000000000000000 : ℚ) / (2425922099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1898787 / 1600000000 : ℚ) + (762401011 / 500000000000 : ℚ) ≤
        (757892749 / 100000000000 : ℚ) := by norm_num only
    have hc : (((603134059 / 500000000000 : ℚ) +
        (10957131227 / 1000000000000000000 : ℚ) / (2425922099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1898787 / 1600000000 : ℚ) + (762401011 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((757892749 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11988]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11988 :
    2 * 160 < 11988 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995101 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11988 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11989 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11989. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11989 : WorldParameters where
  hiddenCharge := (301553793 / 250000000000 : ℝ)
  frame := (318033519909 / 500000000000 : ℝ)
  moment := (5477368439 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11989 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470175903267 / 1000000000000 : ℝ)
    root := (1443026401 / 200000000000 : ℝ) }

noncomputable def scalar11989 : ScalarCertificate 11989 world11989 agent11989 where
  dimensionLo := 11989
  dimensionHi := 11989
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2426337199 / 1000000000000 : ℝ)
  frameLo := (318033519909 / 500000000000 : ℝ)
  frameHi := (1470175903267 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11989]
  agentFrame_pos := by norm_num only [agent11989]
  worldRadius := (2426337199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11989]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (296420523 / 250000000000 : ℝ)
  lowerTail := (1523542103 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7575511063 / 1000000000000 : ℝ)
  ledger := by
    have h : (301553793 / 250000000000 : ℚ) +
        (5477368439 / 500000000000000000 : ℚ) / (2426337199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (296420523 / 250000000000 : ℚ) + (1523542103 / 1000000000000 : ℚ) ≤
        (7575511063 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((301553793 / 250000000000 : ℚ) +
        (5477368439 / 500000000000000000 : ℚ) / (2426337199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (296420523 / 250000000000 : ℚ) + (1523542103 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7575511063 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11989]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11989 :
    2 * 160 < 11989 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995199 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11989 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11990 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11990. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11990 : WorldParameters where
  hiddenCharge := (1206162241 / 1000000000000 : ℝ)
  frame := (318025730967 / 500000000000 : ℝ)
  moment := (547617163 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11990 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183766418271 / 125000000000 : ℝ)
    root := (7214473029 / 1000000000000 : ℝ) }

noncomputable def scalar11990 : ScalarCertificate 11990 world11990 agent11990 where
  dimensionLo := 11990
  dimensionHi := 11990
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2426752299 / 1000000000000 : ℝ)
  frameLo := (318025730967 / 500000000000 : ℝ)
  frameHi := (183766418271 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11990]
  agentFrame_pos := by norm_num only [agent11990]
  worldRadius := (2426752299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11990]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (296155869 / 250000000000 : ℝ)
  lowerTail := (761141743 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (151441957 / 20000000000 : ℝ)
  ledger := by
    have h : (1206162241 / 1000000000000 : ℚ) +
        (547617163 / 50000000000000000 : ℚ) / (2426752299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (296155869 / 250000000000 : ℚ) + (761141743 / 500000000000 : ℚ) ≤
        (151441957 / 20000000000 : ℚ) := by norm_num only
    have hc : (((1206162241 / 1000000000000 : ℚ) +
        (547617163 / 50000000000000000 : ℚ) / (2426752299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (296155869 / 250000000000 : ℚ) + (761141743 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((151441957 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11990]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11990 :
    2 * 160 < 11990 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997273 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11990 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11991 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11991. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11991 : WorldParameters where
  hiddenCharge := (301527331 / 250000000000 : ℝ)
  frame := (636035886731 / 1000000000000 : ℝ)
  moment := (2737487593 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11991 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (294017361347 / 200000000000 : ℝ)
    root := (180345357 / 25000000000 : ℝ) }

noncomputable def scalar11991 : ScalarCertificate 11991 world11991 agent11991 where
  dimensionLo := 11991
  dimensionHi := 11991
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2427167499 / 1000000000000 : ℝ)
  frameLo := (636035886731 / 1000000000000 : ℝ)
  frameHi := (294017361347 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11991]
  agentFrame_pos := by norm_num only [agent11991]
  worldRadius := (2427167499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11991]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1183566019 / 1000000000000 : ℝ)
  lowerTail := (1521026167 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3784343841 / 500000000000 : ℝ)
  ledger := by
    have h : (301527331 / 250000000000 : ℚ) +
        (2737487593 / 250000000000000000 : ℚ) / (2427167499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1183566019 / 1000000000000 : ℚ) + (1521026167 / 1000000000000 : ℚ) ≤
        (3784343841 / 500000000000 : ℚ) := by norm_num only
    have hc : (((301527331 / 250000000000 : ℚ) +
        (2737487593 / 250000000000000000 : ℚ) / (2427167499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1183566019 / 1000000000000 : ℚ) + (1521026167 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3784343841 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11991]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11991 :
    2 * 160 < 11991 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999019 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11991 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11992 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11992. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11992 : WorldParameters where
  hiddenCharge := (1206056423 / 1000000000000 : ℝ)
  frame := (19875634819 / 31250000000 : ℝ)
  moment := (2189511643 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11992 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1470042296841 / 1000000000000 : ℝ)
    root := (7213155759 / 1000000000000 : ℝ) }

noncomputable def scalar11992 : ScalarCertificate 11992 world11992 agent11992 where
  dimensionLo := 11992
  dimensionHi := 11992
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2427582499 / 1000000000000 : ℝ)
  frameLo := (19875634819 / 31250000000 : ℝ)
  frameHi := (1470042296841 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11992]
  agentFrame_pos := by norm_num only [agent11992]
  worldRadius := (2427582499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11992]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (236501911 / 200000000000 : ℝ)
  lowerTail := (1519769951 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7565280661 / 1000000000000 : ℝ)
  ledger := by
    have h : (1206056423 / 1000000000000 : ℚ) +
        (2189511643 / 200000000000000000 : ℚ) / (2427582499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (236501911 / 200000000000 : ℚ) + (1519769951 / 1000000000000 : ℚ) ≤
        (7565280661 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1206056423 / 1000000000000 : ℚ) +
        (2189511643 / 200000000000000000 : ℚ) / (2427582499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (236501911 / 200000000000 : ℚ) + (1519769951 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7565280661 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11992]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11992 :
    2 * 160 < 11992 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999996779 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11992 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11993 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11993. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11993 : WorldParameters where
  hiddenCharge := (75375221 / 62500000000 : ℝ)
  frame := (127200948873 / 200000000000 : ℝ)
  moment := (2736291697 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11993 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1469997804587 / 1000000000000 : ℝ)
    root := (3606248693 / 500000000000 : ℝ) }

noncomputable def scalar11993 : ScalarCertificate 11993 world11993 agent11993 where
  dimensionLo := 11993
  dimensionHi := 11993
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2427997699 / 1000000000000 : ℝ)
  frameLo := (127200948873 / 200000000000 : ℝ)
  frameHi := (1469997804587 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11993]
  agentFrame_pos := by norm_num only [agent11993]
  worldRadius := (2427997699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11993]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1181454263 / 1000000000000 : ℝ)
  lowerTail := (1518515053 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1512375313 / 200000000000 : ℝ)
  ledger := by
    have h : (75375221 / 62500000000 : ℚ) +
        (2736291697 / 250000000000000000 : ℚ) / (2427997699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1181454263 / 1000000000000 : ℚ) + (1518515053 / 1000000000000 : ℚ) ≤
        (1512375313 / 200000000000 : ℚ) := by norm_num only
    have hc : (((75375221 / 62500000000 : ℚ) +
        (2736291697 / 250000000000000000 : ℚ) / (2427997699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1181454263 / 1000000000000 : ℚ) + (1518515053 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1512375313 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11993]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11993 :
    2 * 160 < 11993 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999951 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11993 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11994 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11994. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11994 : WorldParameters where
  hiddenCharge := (150743833 / 125000000000 : ℝ)
  frame := (1589972943 / 2500000000 : ℝ)
  moment := (1094277609 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11994 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (734976670923 / 500000000000 : ℝ)
    root := (7211839317 / 1000000000000 : ℝ) }

noncomputable def scalar11994 : ScalarCertificate 11994 world11994 agent11994 where
  dimensionLo := 11994
  dimensionHi := 11994
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2428412799 / 1000000000000 : ℝ)
  frameLo := (1589972943 / 2500000000 : ℝ)
  frameHi := (734976670923 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11994]
  agentFrame_pos := by norm_num only [agent11994]
  worldRadius := (2428412799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11994]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (295100021 / 250000000000 : ℝ)
  lowerTail := (758630699 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7558475721 / 1000000000000 : ℝ)
  ledger := by
    have h : (150743833 / 125000000000 : ℚ) +
        (1094277609 / 100000000000000000 : ℚ) / (2428412799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (295100021 / 250000000000 : ℚ) + (758630699 / 500000000000 : ℚ) ≤
        (7558475721 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((150743833 / 125000000000 : ℚ) +
        (1094277609 / 100000000000000000 : ℚ) / (2428412799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (295100021 / 250000000000 : ℚ) + (758630699 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7558475721 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11994]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11994 :
    2 * 160 < 11994 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995661 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11994 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11995 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11995. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11995 : WorldParameters where
  hiddenCharge := (75368613 / 62500000000 : ℝ)
  frame := (635973612713 / 1000000000000 : ℝ)
  moment := (5470193061 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11995 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1469908896719 / 1000000000000 : ℝ)
    root := (1802795369 / 250000000000 : ℝ) }

noncomputable def scalar11995 : ScalarCertificate 11995 world11995 agent11995 where
  dimensionLo := 11995
  dimensionHi := 11995
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2428827899 / 1000000000000 : ℝ)
  frameLo := (635973612713 / 1000000000000 : ℝ)
  frameHi := (1469908896719 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11995]
  agentFrame_pos := by norm_num only [agent11995]
  worldRadius := (2428827899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11995]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (117934699 / 100000000000 : ℝ)
  lowerTail := (1516008951 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7555077909 / 1000000000000 : ℝ)
  ledger := by
    have h : (75368613 / 62500000000 : ℚ) +
        (5470193061 / 500000000000000000 : ℚ) / (2428827899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (117934699 / 100000000000 : ℚ) + (1516008951 / 1000000000000 : ℚ) ≤
        (7555077909 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((75368613 / 62500000000 : ℚ) +
        (5470193061 / 500000000000000000 : ℚ) / (2428827899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (117934699 / 100000000000 : ℚ) + (1516008951 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7555077909 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11995]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11995 :
    2 * 160 < 11995 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999591 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11995 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11996 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11996. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11996 : WorldParameters where
  hiddenCharge := (241168993 / 200000000000 : ℝ)
  frame := (79494756363 / 125000000000 : ℝ)
  moment := (10937996883 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11996 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (2870829053 / 1953125000 : ℝ)
    root := (360526193 / 50000000000 : ℝ) }

noncomputable def scalar11996 : ScalarCertificate 11996 world11996 agent11996 where
  dimensionLo := 11996
  dimensionHi := 11996
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2429242999 / 1000000000000 : ℝ)
  frameLo := (79494756363 / 125000000000 : ℝ)
  frameHi := (2870829053 / 1953125000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11996]
  agentFrame_pos := by norm_num only [agent11996]
  worldRadius := (2429242999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11996]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (235659 / 200000000 : ℝ)
  lowerTail := (1514757739 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7551683179 / 1000000000000 : ℝ)
  ledger := by
    have h : (241168993 / 200000000000 : ℚ) +
        (10937996883 / 1000000000000000000 : ℚ) / (2429242999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (235659 / 200000000 : ℚ) + (1514757739 / 1000000000000 : ℚ) ≤
        (7551683179 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((241168993 / 200000000000 : ℚ) +
        (10937996883 / 1000000000000000000 : ℚ) / (2429242999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (235659 / 200000000 : ℚ) + (1514757739 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7551683179 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11996]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11996 :
    2 * 160 < 11996 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1099999687 / 100000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11996 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11997 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11997. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11997 : WorldParameters where
  hiddenCharge := (602896069 / 500000000000 : ℝ)
  frame := (635942491771 / 1000000000000 : ℝ)
  moment := (10935608373 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11997 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1469820077083 / 1000000000000 : ℝ)
    root := (7209866393 / 1000000000000 : ℝ) }

noncomputable def scalar11997 : ScalarCertificate 11997 world11997 agent11997 where
  dimensionLo := 11997
  dimensionHi := 11997
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2429658099 / 1000000000000 : ℝ)
  frameLo := (635942491771 / 1000000000000 : ℝ)
  frameHi := (1469820077083 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11997]
  agentFrame_pos := by norm_num only [agent11997]
  worldRadius := (2429658099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11997]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1177244059 / 1000000000000 : ℝ)
  lowerTail := (1513507703 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1887072853 / 250000000000 : ℝ)
  ledger := by
    have h : (602896069 / 500000000000 : ℚ) +
        (10935608373 / 1000000000000000000 : ℚ) / (2429658099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1177244059 / 1000000000000 : ℚ) + (1513507703 / 1000000000000 : ℚ) ≤
        (1887072853 / 250000000000 : ℚ) := by norm_num only
    have hc : (((602896069 / 500000000000 : ℚ) +
        (10935608373 / 1000000000000000000 : ℚ) / (2429658099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1177244059 / 1000000000000 : ℚ) + (1513507703 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1887072853 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11997]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11997 :
    2 * 160 < 11997 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998029 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11997 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11998 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11998. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11998 : WorldParameters where
  hiddenCharge := (602869663 / 500000000000 : ℝ)
  frame := (317963467657 / 500000000000 : ℝ)
  moment := (683326287 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11998 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1469775702549 / 1000000000000 : ℝ)
    root := (720920923 / 100000000000 : ℝ) }

noncomputable def scalar11998 : ScalarCertificate 11998 world11998 agent11998 where
  dimensionLo := 11998
  dimensionHi := 11998
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2430073099 / 1000000000000 : ℝ)
  frameLo := (317963467657 / 500000000000 : ℝ)
  frameHi := (1469775702549 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11998]
  agentFrame_pos := by norm_num only [agent11998]
  worldRadius := (2430073099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11998]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (235238841 / 200000000000 : ℝ)
  lowerTail := (12098071 / 8000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7544902833 / 1000000000000 : ℝ)
  ledger := by
    have h : (602869663 / 500000000000 : ℚ) +
        (683326287 / 62500000000000000 : ℚ) / (2430073099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (235238841 / 200000000000 : ℚ) + (12098071 / 8000000000 : ℚ) ≤
        (7544902833 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((602869663 / 500000000000 : ℚ) +
        (683326287 / 62500000000000000 : ℚ) / (2430073099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (235238841 / 200000000000 : ℚ) + (12098071 / 8000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7544902833 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11998]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11998 :
    2 * 160 < 11998 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997131 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11998 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11999 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11999. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11999 : WorldParameters where
  hiddenCharge := (4709713 / 3906250000 : ℝ)
  frame := (158977845383 / 250000000000 : ℝ)
  moment := (5465416769 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11999 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (734865672789 / 500000000000 : ℝ)
    root := (7208552293 / 1000000000000 : ℝ) }

noncomputable def scalar11999 : ScalarCertificate 11999 world11999 agent11999 where
  dimensionLo := 11999
  dimensionHi := 11999
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2430488299 / 1000000000000 : ℝ)
  frameLo := (158977845383 / 250000000000 : ℝ)
  frameHi := (734865672789 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11999]
  agentFrame_pos := by norm_num only [agent11999]
  worldRadius := (2430488299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11999]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1175145569 / 1000000000000 : ℝ)
  lowerTail := (302202283 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7541517271 / 1000000000000 : ℝ)
  ledger := by
    have h : (4709713 / 3906250000 : ℚ) +
        (5465416769 / 500000000000000000 : ℚ) / (2430488299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1175145569 / 1000000000000 : ℚ) + (302202283 / 200000000000 : ℚ) ≤
        (7541517271 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((4709713 / 3906250000 : ℚ) +
        (5465416769 / 500000000000000000 : ℚ) / (2430488299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1175145569 / 1000000000000 : ℚ) + (302202283 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7541517271 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11999]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11999 :
    2 * 160 < 11999 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (87999979 / 8000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11999 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12000 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12000. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12000 : WorldParameters where
  hiddenCharge := (602816873 / 500000000000 : ℝ)
  frame := (79486978803 / 125000000000 : ℝ)
  moment := (10940618987 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12000 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (753970496467 / 500000000000 : ℝ)
    root := (237539247 / 31250000000 : ℝ) }

noncomputable def scalar12000 : ScalarCertificate 12000 world12000 agent12000 where
  dimensionLo := 12000
  dimensionHi := 12000
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2269132499 / 1000000000000 : ℝ)
  frameLo := (79486978803 / 125000000000 : ℝ)
  frameHi := (753970496467 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12000]
  agentFrame_pos := by norm_num only [agent12000]
  worldRadius := (2269132499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12000]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (18832709 / 12500000000 : ℝ)
  lowerTail := (23652211 / 12500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4264196759 / 500000000000 : ℝ)
  ledger := by
    have h : (602816873 / 500000000000 : ℚ) +
        (10940618987 / 1000000000000000000 : ℚ) / (2269132499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (18832709 / 12500000000 : ℚ) + (23652211 / 12500000000 : ℚ) ≤
        (4264196759 / 500000000000 : ℚ) := by norm_num only
    have hc : (((602816873 / 500000000000 : ℚ) +
        (10940618987 / 1000000000000000000 : ℚ) / (2269132499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (18832709 / 12500000000 : ℚ) + (23652211 / 12500000000 : ℚ) : ℚ) : ℝ) ≤
        ((4264196759 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12000]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12000 :
    2 * 160 < 12000 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999449 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12000 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12001 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12001. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12001 : WorldParameters where
  hiddenCharge := (602790489 / 500000000000 : ℝ)
  frame := (63588028199 / 100000000000 : ℝ)
  moment := (437529251 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12001 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1507889056963 / 1000000000000 : ℝ)
    root := (7600550783 / 1000000000000 : ℝ) }

noncomputable def scalar12001 : ScalarCertificate 12001 world12001 agent12001 where
  dimensionLo := 12001
  dimensionHi := 12001
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2269533799 / 1000000000000 : ℝ)
  frameLo := (63588028199 / 100000000000 : ℝ)
  frameHi := (1507889056963 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12001]
  agentFrame_pos := by norm_num only [agent12001]
  worldRadius := (2269533799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12001]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (188154811 / 125000000000 : ℝ)
  lowerTail := (1890571747 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (66594863 / 7812500000 : ℝ)
  ledger := by
    have h : (602790489 / 500000000000 : ℚ) +
        (437529251 / 40000000000000000 : ℚ) / (2269533799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (188154811 / 125000000000 : ℚ) + (1890571747 / 1000000000000 : ℚ) ≤
        (66594863 / 7812500000 : ℚ) := by norm_num only
    have hc : (((602790489 / 500000000000 : ℚ) +
        (437529251 / 40000000000000000 : ℚ) / (2269533799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (188154811 / 125000000000 : ℚ) + (1890571747 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((66594863 / 7812500000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12001]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12001 :
    2 * 160 < 12001 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994531 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12001 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12002 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12002. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12002 : WorldParameters where
  hiddenCharge := (48221129 / 40000000000 : ℝ)
  frame := (158966184057 / 250000000000 : ℝ)
  moment := (10935844291 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12002 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (753918573511 / 500000000000 : ℝ)
    root := (3799922949 / 500000000000 : ℝ) }

noncomputable def scalar12002 : ScalarCertificate 12002 world12002 agent12002 where
  dimensionLo := 12002
  dimensionHi := 12002
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2269935199 / 1000000000000 : ℝ)
  frameLo := (158966184057 / 250000000000 : ℝ)
  frameHi := (753918573511 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12002]
  agentFrame_pos := by norm_num only [agent12002]
  worldRadius := (2269935199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12002]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1503861801 / 1000000000000 : ℝ)
  lowerTail := (1888968313 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1064986919 / 125000000000 : ℝ)
  ledger := by
    have h : (48221129 / 40000000000 : ℚ) +
        (10935844291 / 1000000000000000000 : ℚ) / (2269935199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1503861801 / 1000000000000 : ℚ) + (1888968313 / 1000000000000 : ℚ) ≤
        (1064986919 / 125000000000 : ℚ) := by norm_num only
    have hc : (((48221129 / 40000000000 : ℚ) +
        (10935844291 / 1000000000000000000 : ℚ) / (2269935199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1503861801 / 1000000000000 : ℚ) + (1888968313 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1064986919 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12002]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12002 :
    2 * 160 < 12002 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994439 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12002 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12003 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12003. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12003 : WorldParameters where
  hiddenCharge := (602737743 / 500000000000 : ℝ)
  frame := (635849193139 / 1000000000000 : ℝ)
  moment := (5466729017 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12003 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (94236578943 / 62500000000 : ℝ)
    root := (759914117 / 100000000000 : ℝ) }

noncomputable def scalar12003 : ScalarCertificate 12003 world12003 agent12003 where
  dimensionLo := 12003
  dimensionHi := 12003
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2270336599 / 1000000000000 : ℝ)
  frameLo := (635849193139 / 1000000000000 : ℝ)
  frameHi := (94236578943 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12003]
  agentFrame_pos := by norm_num only [agent12003]
  worldRadius := (2270336599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12003]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (300497301 / 200000000000 : ℝ)
  lowerTail := (377473281 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8515652037 / 1000000000000 : ℝ)
  ledger := by
    have h : (602737743 / 500000000000 : ℚ) +
        (5466729017 / 500000000000000000 : ℚ) / (2270336599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (300497301 / 200000000000 : ℚ) + (377473281 / 200000000000 : ℚ) ≤
        (8515652037 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((602737743 / 500000000000 : ℚ) +
        (5466729017 / 500000000000000000 : ℚ) / (2270336599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (300497301 / 200000000000 : ℚ) + (377473281 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8515652037 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12003]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12003 :
    2 * 160 < 12003 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (219999983 / 20000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12003 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12004 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12004. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12004 : WorldParameters where
  hiddenCharge := (1205422763 / 1000000000000 : ℝ)
  frame := (635833652721 / 1000000000000 : ℝ)
  moment := (5465536253 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12004 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (376933354333 / 250000000000 : ℝ)
    root := (1519687351 / 200000000000 : ℝ) }

noncomputable def scalar12004 : ScalarCertificate 12004 world12004 agent12004 where
  dimensionLo := 12004
  dimensionHi := 12004
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2270737899 / 1000000000000 : ℝ)
  frameLo := (635833652721 / 1000000000000 : ℝ)
  frameHi := (376933354333 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12004]
  agentFrame_pos := by norm_num only [agent12004]
  worldRadius := (2270737899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12004]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (15011127 / 10000000000 : ℝ)
  lowerTail := (235720767 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (212785323 / 25000000000 : ℝ)
  ledger := by
    have h : (1205422763 / 1000000000000 : ℚ) +
        (5465536253 / 500000000000000000 : ℚ) / (2270737899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (15011127 / 10000000000 : ℚ) + (235720767 / 125000000000 : ℚ) ≤
        (212785323 / 25000000000 : ℚ) := by norm_num only
    have hc : (((1205422763 / 1000000000000 : ℚ) +
        (5465536253 / 500000000000000000 : ℚ) / (2270737899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (15011127 / 10000000000 : ℚ) + (235720767 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((212785323 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12004]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12004 :
    2 * 160 < 12004 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (549999839 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12004 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12005 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12005. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12005 : WorldParameters where
  hiddenCharge := (602685027 / 500000000000 : ℝ)
  frame := (317909057487 / 500000000000 : ℝ)
  moment := (1366085963 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12005 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (47115049923 / 31250000000 : ℝ)
    root := (237429143 / 31250000000 : ℝ) }

noncomputable def scalar12005 : ScalarCertificate 12005 world12005 agent12005 where
  dimensionLo := 12005
  dimensionHi := 12005
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2271139199 / 1000000000000 : ℝ)
  frameLo := (317909057487 / 500000000000 : ℝ)
  frameHi := (47115049923 / 31250000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12005]
  agentFrame_pos := by norm_num only [agent12005]
  worldRadius := (2271139199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12005]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1499740349 / 1000000000000 : ℝ)
  lowerTail := (94208373 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (850717773 / 100000000000 : ℝ)
  ledger := by
    have h : (602685027 / 500000000000 : ℚ) +
        (1366085963 / 125000000000000000 : ℚ) / (2271139199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1499740349 / 1000000000000 : ℚ) + (94208373 / 50000000000 : ℚ) ≤
        (850717773 / 100000000000 : ℚ) := by norm_num only
    have hc : (((602685027 / 500000000000 : ℚ) +
        (1366085963 / 125000000000000000 : ℚ) / (2271139199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1499740349 / 1000000000000 : ℚ) + (94208373 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((850717773 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12005]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12005 :
    2 * 160 < 12005 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999159 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12005 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12006 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12006. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12006 : WorldParameters where
  hiddenCharge := (15066467 / 12500000000 : ℝ)
  frame := (635802579897 / 1000000000000 : ℝ)
  moment := (10926303629 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12006 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1507629815869 / 1000000000000 : ℝ)
    root := (7597028553 / 1000000000000 : ℝ) }

noncomputable def scalar12006 : ScalarCertificate 12006 world12006 agent12006 where
  dimensionLo := 12006
  dimensionHi := 12006
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2271540499 / 1000000000000 : ℝ)
  frameLo := (635802579897 / 1000000000000 : ℝ)
  frameHi := (1507629815869 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12006]
  agentFrame_pos := by norm_num only [agent12006]
  worldRadius := (2271540499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12006]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1498369437 / 1000000000000 : ℝ)
  lowerTail := (235321297 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (8502946451 / 1000000000000 : ℝ)
  ledger := by
    have h : (15066467 / 12500000000 : ℚ) +
        (10926303629 / 1000000000000000000 : ℚ) / (2271540499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1498369437 / 1000000000000 : ℚ) + (235321297 / 125000000000 : ℚ) ≤
        (8502946451 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((15066467 / 12500000000 : ℚ) +
        (10926303629 / 1000000000000000000 : ℚ) / (2271540499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1498369437 / 1000000000000 : ℚ) + (235321297 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((8502946451 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12006]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12006 :
    2 * 160 < 12006 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997197 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12006 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12007 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12007. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12007 : WorldParameters where
  hiddenCharge := (1205264681 / 1000000000000 : ℝ)
  frame := (635787047489 / 1000000000000 : ℝ)
  moment := (273098007 / 25000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12007 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (376894515029 / 250000000000 : ℝ)
    root := (1899081211 / 250000000000 : ℝ) }

noncomputable def scalar12007 : ScalarCertificate 12007 world12007 agent12007 where
  dimensionLo := 12007
  dimensionHi := 12007
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2271941899 / 1000000000000 : ℝ)
  frameLo := (635787047489 / 1000000000000 : ℝ)
  frameHi := (376894515029 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12007]
  agentFrame_pos := by norm_num only [agent12007]
  worldRadius := (2271941899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12007]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (149700013 / 100000000000 : ℝ)
  lowerTail := (470243763 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (849871923 / 100000000000 : ℝ)
  ledger := by
    have h : (1205264681 / 1000000000000 : ℚ) +
        (273098007 / 25000000000000000 : ℚ) / (2271941899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (149700013 / 100000000000 : ℚ) + (470243763 / 250000000000 : ℚ) ≤
        (849871923 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1205264681 / 1000000000000 : ℚ) +
        (273098007 / 25000000000000000 : ℚ) / (2271941899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (149700013 / 100000000000 : ℚ) + (470243763 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((849871923 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12007]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12007 :
    2 * 160 < 12007 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (439999773 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12007 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12008 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12008. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12008 : WorldParameters where
  hiddenCharge := (1205212017 / 1000000000000 : ℝ)
  frame := (635771517749 / 1000000000000 : ℝ)
  moment := (5460768829 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12008 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (753763165127 / 500000000000 : ℝ)
    root := (7595621369 / 1000000000000 : ℝ) }

noncomputable def scalar12008 : ScalarCertificate 12008 world12008 agent12008 where
  dimensionLo := 12008
  dimensionHi := 12008
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2272343199 / 1000000000000 : ℝ)
  frameLo := (635771517749 / 1000000000000 : ℝ)
  frameHi := (753763165127 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12008]
  agentFrame_pos := by norm_num only [agent12008]
  worldRadius := (2272343199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12008]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (186954023 / 125000000000 : ℝ)
  lowerTail := (1879381217 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4247247961 / 500000000000 : ℝ)
  ledger := by
    have h : (1205212017 / 1000000000000 : ℚ) +
        (5460768829 / 500000000000000000 : ℚ) / (2272343199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (186954023 / 125000000000 : ℚ) + (1879381217 / 1000000000000 : ℚ) ≤
        (4247247961 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1205212017 / 1000000000000 : ℚ) +
        (5460768829 / 500000000000000000 : ℚ) / (2272343199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (186954023 / 125000000000 : ℚ) + (1879381217 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4247247961 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12008]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12008 :
    2 * 160 < 12008 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999998929 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 12008 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding11984 :
    (1206480050720621582683 / 1000000000000000000000000 : ℝ) ≤ world11984.hiddenCharge ∧
    (636144969476739036372073 / 1000000000000000000000000 : ℝ) ≤ world11984.frame ∧
    (5483357969 / 500000000000000000 : ℝ) ≤ world11984.moment ∧
    (1470399031460400824618367 / 1000000000000000000000000 : ℝ) ≤ agent11984.frame ∧
    (902303806595266216531 / 125000000000000000000000 : ℝ) ≤ agent11984.root ∧
    scalar11984.worldRadius ≤ (2424261699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (630182591873981946571 / 500000000000000000000000 : ℝ) ≤ agent11984.charge ∧
    (297747988098393440309 / 250000000000000000000000 : ℝ) ≤ scalar11984.upperTail ∧
    (1529853929800597856333 / 1000000000000000000000000 : ℝ) ≤ scalar11984.lowerTail ∧
    scalar11984.totalBudget ≤ (759262383272675279571 / 100000000000000000000000 : ℝ) := by
  norm_num only [world11984, agent11984, scalar11984] <;> simp only [true_and]

theorem source_rounding11985 :
    (150803380631247786637 / 125000000000000000000000 : ℝ) ≤ world11985.hiddenCharge ∧
    (636129378177162228885773 / 1000000000000000000000000 : ℝ) ≤ world11985.frame ∧
    (10964318663 / 1000000000000000000 : ℝ) ≤ world11985.moment ∧
    (294070872413250303521439 / 200000000000000000000000 : ℝ) ≤ agent11985.frame ∧
    (3608885130249612334359 / 500000000000000000000000 : ℝ) ≤ agent11985.root ∧
    scalar11985.worldRadius ≤ (2424676699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1260104406201343170163 / 1000000000000000000000000 : ℝ) ≤ agent11985.charge ∧
    (297481914159108554171 / 250000000000000000000000 : ℝ) ≤ scalar11985.upperTail ∧
    (1528588966564726266731 / 1000000000000000000000000 : ℝ) ≤ scalar11985.lowerTail ∧
    scalar11985.totalBudget ≤ (7589195020052723418607 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11985, agent11985, scalar11985] <;> simp only [true_and]

theorem source_rounding11986 :
    (1206374054280490774589 / 1000000000000000000000000 : ℝ) ≤ world11986.hiddenCharge ∧
    (318056894781092972729683 / 500000000000000000000000 : ℝ) ≤ world11986.frame ∧
    (10961922119 / 1000000000000000000 : ℝ) ≤ world11986.moment ∧
    (1470309710400854279771909 / 1000000000000000000000000 : ℝ) ≤ agent11986.frame ∧
    (288684414985990559461 / 40000000000000000000000 : ℝ) ≤ agent11986.root ∧
    scalar11986.worldRadius ≤ (2425091899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (314960971554175043497 / 250000000000000000000000 : ℝ) ≤ agent11986.charge ∧
    (148608081551838371127 / 125000000000000000000000 : ℝ) ≤ scalar11986.upperTail ∧
    (1527325449447561912223 / 1000000000000000000000000 : ℝ) ≤ scalar11986.lowerTail ∧
    scalar11986.totalBudget ≤ (3792884691084332305911 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11986, agent11986, scalar11986] <;> simp only [true_and]

theorem source_rounding11987 :
    (241264215681333179363 / 200000000000000000000000 : ℝ) ≤ world11987.hiddenCharge ∧
    (31804910181553676053621 / 50000000000000000000000 : ℝ) ≤ world11987.frame ∧
    (2739881577 / 250000000000000000 : ℝ) ≤ world11987.moment ∧
    (1470265088342270569871027 / 1000000000000000000000000 : ℝ) ≤ agent11987.frame ∧
    (3608225358268103810503 / 500000000000000000000000 : ℝ) ≤ agent11987.root ∧
    scalar11987.worldRadius ≤ (2425506999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1259583623506246078091 / 1000000000000000000000000 : ℝ) ≤ agent11987.charge ∧
    (593901358297982879337 / 500000000000000000000000 : ℝ) ≤ scalar11987.upperTail ∧
    (1526063126647634934751 / 1000000000000000000000000 : ℝ) ≤ scalar11987.lowerTail ∧
    scalar11987.totalBudget ≤ (3791173454391085683859 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11987, agent11987, scalar11987] <;> simp only [true_and]

theorem source_rounding11988 :
    (301567029355757638683 / 250000000000000000000000 : ℝ) ≤ world11988.hiddenCharge ∧
    (636082620383088608358603 / 1000000000000000000000000 : ℝ) ≤ world11988.frame ∧
    (10957131227 / 1000000000000000000 : ℝ) ≤ world11988.moment ∧
    (367555120996645377778263 / 250000000000000000000000 : ℝ) ≤ agent11988.frame ∧
    (7215791286005718616763 / 1000000000000000000000000 : ℝ) ≤ agent11988.root ∧
    scalar11988.worldRadius ≤ (2425922099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1259323617782552479691 / 1000000000000000000000000 : ℝ) ≤ agent11988.charge ∧
    (74171367126169434839 / 62500000000000000000000 : ℝ) ≤ scalar11988.upperTail ∧
    (762401010594515297759 / 500000000000000000000000 : ℝ) ≤ scalar11988.lowerTail ∧
    scalar11988.totalBudget ≤ (7578927490643857394351 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11988, agent11988, scalar11988] <;> simp only [true_and]

theorem source_rounding11989 :
    (7538844820775670763 / 6250000000000000000000 : ℝ) ≤ world11989.hiddenCharge ∧
    (25442681592699806769827 / 40000000000000000000000 : ℝ) ≤ world11989.frame ∧
    (5477368439 / 500000000000000000 : ℝ) ≤ world11989.moment ∧
    (367543975816530239049863 / 250000000000000000000000 : ℝ) ≤ agent11989.frame ∧
    (1803783001116010843249 / 250000000000000000000000 : ℝ) ≤ agent11989.root ∧
    scalar11989.worldRadius ≤ (2426337199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1259063868758550895243 / 1000000000000000000000000 : ℝ) ≤ agent11989.charge ∧
    (23713641821706615083 / 20000000000000000000000 : ℝ) ≤ scalar11989.upperTail ∧
    (761771051055612659103 / 500000000000000000000000 : ℝ) ≤ scalar11989.lowerTail ∧
    scalar11989.totalBudget ≤ (3787755531654020962949 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11989, agent11989, scalar11989] <;> simp only [true_and]

theorem source_rounding11990 :
    (120616224010442279619 / 100000000000000000000000 : ℝ) ≤ world11990.hiddenCharge ∧
    (318025730966778695474757 / 500000000000000000000000 : ℝ) ≤ world11990.frame ∧
    (547617163 / 50000000000000000 : ℝ) ≤ world11990.moment ∧
    (1470131346167739871473689 / 1000000000000000000000000 : ℝ) ≤ agent11990.frame ∧
    (180361825716459948811 / 25000000000000000000000 : ℝ) ≤ agent11990.root ∧
    scalar11990.worldRadius ≤ (2426752299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (157350547018441532091 / 125000000000000000000000 : ℝ) ≤ agent11990.charge ∧
    (1184623475282066655433 / 1000000000000000000000000 : ℝ) ≤ scalar11990.upperTail ∧
    (190285435748558124197 / 125000000000000000000000 : ℝ) ≤ scalar11990.lowerTail ∧
    scalar11990.totalBudget ≤ (7572097850588818038633 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11990, agent11990, scalar11990] <;> simp only [true_and]

theorem source_rounding11991 :
    (1206109323758506147167 / 1000000000000000000000000 : ℝ) ≤ world11991.hiddenCharge ∧
    (159008971682634946072653 / 250000000000000000000000 : ℝ) ≤ world11991.frame ∧
    (2737487593 / 250000000000000000 : ℝ) ≤ world11991.moment ∧
    (1470086806734107642258229 / 1000000000000000000000000 : ℝ) ≤ agent11991.frame ∧
    (901726784997288601237 / 125000000000000000000000 : ℝ) ≤ agent11991.root ∧
    scalar11991.worldRadius ≤ (2427167499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (314636284915786602179 / 250000000000000000000000 : ℝ) ≤ agent11991.charge ∧
    (147945752362497292311 / 125000000000000000000000 : ℝ) ≤ scalar11991.upperTail ∧
    (190128270750856940941 / 125000000000000000000000 : ℝ) ≤ scalar11991.lowerTail ∧
    scalar11991.totalBudget ≤ (3784343841274481596487 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11991, agent11991, scalar11991] <;> simp only [true_and]

theorem source_rounding11992 :
    (241211284456177534259 / 200000000000000000000000 : ℝ) ≤ world11992.hiddenCharge ∧
    (159005078551926758613017 / 250000000000000000000000 : ℝ) ≤ world11992.frame ∧
    (2189511643 / 200000000000000000 : ℝ) ≤ world11992.moment ∧
    (1470042296840762871860049 / 1000000000000000000000000 : ℝ) ≤ agent11992.frame ∧
    (1803288939567902141581 / 250000000000000000000000 : ℝ) ≤ agent11992.root ∧
    scalar11992.worldRadius ≤ (2427582499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (629143079509700803111 / 500000000000000000000000 : ℝ) ≤ agent11992.charge ∧
    (118250955428062154341 / 100000000000000000000000 : ℝ) ≤ scalar11992.upperTail ∧
    (1519769950460629201919 / 1000000000000000000000000 : ℝ) ≤ scalar11992.lowerTail ∧
    scalar11992.totalBudget ≤ (1891320165361629585919 / 250000000000000000000000 : ℝ) := by
  norm_num only [world11992, agent11992, scalar11992] <;> simp only [true_and]

theorem source_rounding11993 :
    (603001767833052285151 / 500000000000000000000000 : ℝ) ≤ world11993.hiddenCharge ∧
    (318002372182162136715117 / 500000000000000000000000 : ℝ) ≤ world11993.frame ∧
    (2736291697 / 250000000000000000 : ℝ) ≤ world11993.moment ∧
    (73499890229323451459711 / 50000000000000000000000 : ℝ) ≤ agent11993.frame ∧
    (7212497385010993418619 / 1000000000000000000000000 : ℝ) ≤ agent11993.root ∧
    scalar11993.worldRadius ≤ (2427997699999999999999 / 1000000000000000000000000 : ℝ) ∧
    (629013716965332006673 / 500000000000000000000000 : ℝ) ≤ agent11993.charge ∧
    (1181454262285309983779 / 1000000000000000000000000 : ℝ) ≤ scalar11993.upperTail ∧
    (3796287630899413093 / 2500000000000000000000 : ℝ) ≤ scalar11993.lowerTail ∧
    scalar11993.totalBudget ≤ (3780938282888492992261 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11993, agent11993, scalar11993] <;> simp only [true_and]

theorem source_rounding11994 :
    (1205950663908689390277 / 1000000000000000000000000 : ℝ) ≤ world11994.hiddenCharge ∧
    (635989177199656770670687 / 1000000000000000000000000 : ℝ) ≤ world11994.frame ∧
    (1094277609 / 100000000000000000 : ℝ) ≤ world11994.moment ∧
    (734976670922878807642141 / 500000000000000000000000 : ℝ) ≤ agent11994.frame ∧
    (3605919658405880995713 / 500000000000000000000000 : ℝ) ≤ agent11994.root ∧
    scalar11994.worldRadius ≤ (2428412799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (314442241027914300671 / 250000000000000000000000 : ℝ) ≤ agent11994.charge ∧
    (590200041882519276757 / 500000000000000000000000 : ℝ) ≤ scalar11994.upperTail ∧
    (189657674708501790739 / 125000000000000000000000 : ℝ) ≤ scalar11994.lowerTail ∧
    scalar11994.totalBudget ≤ (7558475721964277266669 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11994, agent11994, scalar11994] <;> simp only [true_and]

theorem source_rounding11995 :
    (1205897807003183023963 / 1000000000000000000000000 : ℝ) ≤ world11995.hiddenCharge ∧
    (635973612712970075830357 / 1000000000000000000000000 : ℝ) ≤ world11995.frame ∧
    (5470193061 / 500000000000000000 : ℝ) ≤ world11995.moment ∧
    (1469908896718463029291101 / 1000000000000000000000000 : ℝ) ≤ agent11995.frame ∧
    (3605590737565205817321 / 500000000000000000000000 : ℝ) ≤ agent11995.root ∧
    scalar11995.worldRadius ≤ (2428827899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (628755374638730827767 / 500000000000000000000000 : ℝ) ≤ agent11995.charge ∧
    (235869397839944319541 / 200000000000000000000000 : ℝ) ≤ scalar11995.upperTail ∧
    (1516008950494437832011 / 1000000000000000000000000 : ℝ) ≤ scalar11995.lowerTail ∧
    scalar11995.totalBudget ≤ (1511015581927670799281 / 200000000000000000000000 : ℝ) := by
  norm_num only [world11995, agent11995, scalar11995] <;> simp only [true_and]

theorem source_rounding11996 :
    (1205844964944127484057 / 1000000000000000000000000 : ℝ) ≤ world11996.hiddenCharge ∧
    (635958050903530123809519 / 1000000000000000000000000 : ℝ) ≤ world11996.frame ∧
    (10937996883 / 1000000000000000000 : ℝ) ≤ world11996.moment ∧
    (734932237567605365207721 / 500000000000000000000000 : ℝ) ≤ agent11996.frame ∧
    (3605261929907720446591 / 500000000000000000000000 : ℝ) ≤ agent11996.root ∧
    scalar11996.worldRadius ≤ (2429242999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (314313197285878565719 / 250000000000000000000000 : ℝ) ≤ agent11996.charge ∧
    (7364343745486585643 / 6250000000000000000000 : ℝ) ≤ scalar11996.upperTail ∧
    (1514757738722702561291 / 1000000000000000000000000 : ℝ) ≤ scalar11996.lowerTail ∧
    scalar11996.totalBudget ≤ (3775841589735370007201 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11996, agent11996, scalar11996] <;> simp only [true_and]

theorem source_rounding11997 :
    (602896068863032952587 / 500000000000000000000000 : ℝ) ≤ world11997.hiddenCharge ∧
    (158985622942650761670853 / 250000000000000000000000 : ℝ) ≤ world11997.frame ∧
    (10935608373 / 1000000000000000000 : ℝ) ≤ world11997.moment ∧
    (1469820077082963989726873 / 1000000000000000000000000 : ℝ) ≤ agent11997.frame ∧
    (7209866392406400370449 / 1000000000000000000000000 : ℝ) ≤ agent11997.root ∧
    scalar11997.worldRadius ≤ (2429658099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (628497541712803913559 / 500000000000000000000000 : ℝ) ≤ agent11997.charge ∧
    (117724405869319873501 / 100000000000000000000000 : ℝ) ≤ scalar11997.upperTail ∧
    (47297115699597918793 / 31250000000000000000000 : ℝ) ≤ scalar11997.lowerTail ∧
    scalar11997.totalBudget ≤ (7548291412628634682069 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11997, agent11997, scalar11997] <;> simp only [true_and]

theorem source_rounding11998 :
    (1205739325343543986621 / 1000000000000000000000000 : ℝ) ≤ world11998.hiddenCharge ∧
    (79490866914181888556159 / 125000000000000000000000 : ℝ) ≤ world11998.frame ∧
    (683326287 / 62500000000000000 : ℝ) ≤ world11998.moment ∧
    (1469775702548702103039943 / 1000000000000000000000000 : ℝ) ≤ agent11998.frame ∧
    (3604604614693425572179 / 500000000000000000000000 : ℝ) ≤ agent11998.root ∧
    scalar11998.worldRadius ≤ (2430073099999999999999 / 1000000000000000000000000 : ℝ) ∧
    (7854610198999316029 / 6250000000000000000000 : ℝ) ≤ agent11998.charge ∧
    (1176194204321299850831 / 1000000000000000000000000 : ℝ) ≤ scalar11998.upperTail ∧
    (1512258874620604228069 / 1000000000000000000000000 : ℝ) ≤ scalar11998.lowerTail ∧
    scalar11998.totalBudget ≤ (7544902833270159524133 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11998, agent11998, scalar11998] <;> simp only [true_and]

theorem source_rounding11999 :
    (602843263895554995417 / 500000000000000000000000 : ℝ) ≤ world11999.hiddenCharge ∧
    (635911381531353188126897 / 1000000000000000000000000 : ℝ) ≤ world11999.frame ∧
    (5465416769 / 500000000000000000 : ℝ) ≤ world11999.moment ∧
    (1469731345577297208191561 / 1000000000000000000000000 : ℝ) ≤ agent11999.frame ∧
    (1802138073070041508823 / 250000000000000000000000 : ℝ) ≤ agent11999.root ∧
    scalar11999.worldRadius ≤ (2430488299999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1256480434102865609091 / 1000000000000000000000000 : ℝ) ≤ agent11999.charge ∧
    (1175145568202512462549 / 1000000000000000000000000 : ℝ) ≤ scalar11999.upperTail ∧
    (755505707002085809229 / 500000000000000000000000 : ℝ) ≤ scalar11999.lowerTail ∧
    scalar11999.totalBudget ≤ (7541517271279454881221 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11999, agent11999, scalar11999] <;> simp only [true_and]

theorem source_rounding12000 :
    (301408436265829405161 / 250000000000000000000000 : ℝ) ≤ world12000.hiddenCharge ∧
    (635895830423564137298169 / 1000000000000000000000000 : ℝ) ≤ world12000.frame ∧
    (2188123797226379 / 200000000000000000000000 : ℝ) ≤ world12000.moment ∧
    (301588198586656109675307 / 200000000000000000000000 : ℝ) ≤ agent12000.frame ∧
    (3800627951713701421711 / 500000000000000000000000 : ℝ) ≤ agent12000.root ∧
    scalar12000.worldRadius ≤ (2269132499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1326556733899199914277 / 1000000000000000000000000 : ℝ) ≤ agent12000.charge ∧
    (753308359984000415461 / 500000000000000000000000 : ℝ) ≤ scalar12000.upperTail ∧
    (1892176879416486632687 / 1000000000000000000000000 : ℝ) ≤ scalar12000.lowerTail ∧
    scalar12000.totalBudget ≤ (852839351838525703491 / 100000000000000000000000 : ℝ) := by
  norm_num only [world12000, agent12000, scalar12000] <;> simp only [true_and]

theorem source_rounding12001 :
    (241116195430943763437 / 200000000000000000000000 : ℝ) ≤ world12001.hiddenCharge ∧
    (127176056397871041244551 / 200000000000000000000000 : ℝ) ≤ world12001.frame ∧
    (10938231274224829 / 1000000000000000000000000 : ℝ) ≤ world12001.moment ∧
    (30157781139248983160277 / 20000000000000000000000 : ℝ) ≤ agent12001.frame ∧
    (475034423917757256443 / 62500000000000000000000 : ℝ) ≤ agent12001.root ∧
    scalar12001.worldRadius ≤ (2269533799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (663087280247865266903 / 500000000000000000000000 : ℝ) ≤ agent12001.charge ∧
    (47038702726677110719 / 31250000000000000000000 : ℝ) ≤ scalar12001.upperTail ∧
    (23632146825377646537 / 12500000000000000000000 : ℝ) ≤ scalar12001.lowerTail ∧
    scalar12001.totalBudget ≤ (4262071232111827419537 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12001, agent12001, scalar12001] <;> simp only [true_and]

theorem source_rounding12002 :
    (602764112029935479441 / 500000000000000000000000 : ℝ) ≤ world12002.hiddenCharge ∧
    (127172947245598782708051 / 200000000000000000000000 : ℝ) ≤ world12002.frame ∧
    (10935844290275077 / 1000000000000000000000000 : ℝ) ≤ world12002.moment ∧
    (47119910844424223903949 / 31250000000000000000000 : ℝ) ≤ agent12002.frame ∧
    (949980737195023182121 / 125000000000000000000000 : ℝ) ≤ agent12002.root ∧
    scalar12002.worldRadius ≤ (2269935199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1325792875691042923609 / 1000000000000000000000000 : ℝ) ≤ agent12002.charge ∧
    (1503861800884839414561 / 1000000000000000000000000 : ℝ) ≤ scalar12002.upperTail ∧
    (944484156210450330621 / 500000000000000000000000 : ℝ) ≤ scalar12002.lowerTail ∧
    scalar12002.totalBudget ≤ (532493459507444780993 / 62500000000000000000000 : ℝ) := by
  norm_num only [world12002, agent12002, scalar12002] <;> simp only [true_and]

theorem source_rounding12003 :
    (1205475485773331103683 / 1000000000000000000000000 : ℝ) ≤ world12003.hiddenCharge ∧
    (635849193138748040038857 / 1000000000000000000000000 : ℝ) ≤ world12003.frame ∧
    (10933458033997793 / 1000000000000000000000000 : ℝ) ≤ world12003.moment ∧
    (1507785263087799359386083 / 1000000000000000000000000 : ℝ) ≤ agent12003.frame ∧
    (7599141169183166758123 / 1000000000000000000000000 : ℝ) ≤ agent12003.root ∧
    scalar12003.worldRadius ≤ (2270336599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1325411678738777145183 / 1000000000000000000000000 : ℝ) ≤ agent12003.charge ∧
    (75124325237515330349 / 50000000000000000000000 : ℝ) ≤ scalar12003.upperTail ∧
    (1887366404836843753127 / 1000000000000000000000000 : ℝ) ≤ scalar12003.lowerTail ∧
    scalar12003.totalBudget ≤ (4257826018994735213717 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12003, agent12003, scalar12003] <;> simp only [true_and]

theorem source_rounding12004 :
    (1205422762289660304319 / 1000000000000000000000000 : ℝ) ≤ world12004.hiddenCharge ∧
    (127166730544177121830087 / 200000000000000000000000 : ℝ) ≤ world12004.frame ∧
    (1366384063138541 / 125000000000000000000000 : ℝ) ≤ world12004.moment ∧
    (376933354332834729624679 / 250000000000000000000000 : ℝ) ≤ agent12004.frame ∧
    (3799218377414086593197 / 500000000000000000000000 : ℝ) ≤ agent12004.root ∧
    scalar12004.worldRadius ≤ (2270737899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (331257742223470925653 / 250000000000000000000000 : ℝ) ≤ agent12004.charge ∧
    (750556349806785434951 / 500000000000000000000000 : ℝ) ≤ scalar12004.upperTail ∧
    (942883067626456775863 / 500000000000000000000000 : ℝ) ≤ scalar12004.lowerTail ∧
    scalar12004.totalBudget ≤ (8511412920795891563381 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12004, agent12004, scalar12004] <;> simp only [true_and]

theorem source_rounding12005 :
    (602685026801712519583 / 500000000000000000000000 : ℝ) ≤ world12005.hiddenCharge ∧
    (63581811497367498651633 / 100000000000000000000000 : ℝ) ≤ world12005.frame ∧
    (683042981457643 / 62500000000000000000000 : ℝ) ≤ world12005.moment ∧
    (753840798767590132355431 / 500000000000000000000000 : ℝ) ≤ agent12005.frame ∧
    (7597732575606544185889 / 1000000000000000000000000 : ℝ) ≤ agent12005.root ∧
    scalar12005.worldRadius ≤ (2271139199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1324650745412620985143 / 1000000000000000000000000 : ℝ) ≤ agent12005.charge ∧
    (749870174260537683401 / 500000000000000000000000 : ℝ) ≤ scalar12005.upperTail ∧
    (471041864863159199041 / 250000000000000000000000 : ℝ) ≤ scalar12005.lowerTail ∧
    scalar12005.totalBudget ≤ (8507177730873115097963 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world12005, agent12005, scalar12005] <;> simp only [true_and]

theorem source_rounding12006 :
    (120531735970918859247 / 100000000000000000000000 : ℝ) ≤ world12006.hiddenCharge ∧
    (317901289948192383586441 / 500000000000000000000000 : ℝ) ≤ world12006.frame ∧
    (10926303628355187 / 1000000000000000000000000 : ℝ) ≤ world12006.moment ∧
    (1507629815868435296986501 / 1000000000000000000000000 : ℝ) ≤ agent12006.frame ∧
    (7597028552696116991893 / 1000000000000000000000000 : ℝ) ≤ agent12006.root ∧
    scalar12006.worldRadius ≤ (2271540499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1324271007552552715163 / 1000000000000000000000000 : ℝ) ≤ agent12006.charge ∧
    (374592359203060829249 / 250000000000000000000000 : ℝ) ≤ scalar12006.upperTail ∧
    (1882570375017749612907 / 1000000000000000000000000 : ℝ) ≤ scalar12006.lowerTail ∧
    scalar12006.totalBudget ≤ (4251473225824604464911 / 500000000000000000000000 : ℝ) := by
  norm_num only [world12006, agent12006, scalar12006] <;> simp only [true_and]

theorem source_rounding12007 :
    (602632340300760554167 / 500000000000000000000000 : ℝ) ≤ world12007.hiddenCharge ∧
    (635787047488283818878361 / 1000000000000000000000000 : ℝ) ≤ world12007.frame ∧
    (10923920279922851 / 1000000000000000000000000 : ℝ) ≤ world12007.moment ∧
    (75378903005765674062373 / 50000000000000000000000 : ℝ) ≤ agent12007.frame ∧
    (1899081210818242535153 / 250000000000000000000000 : ℝ) ≤ agent12007.root ∧
    scalar12007.worldRadius ≤ (2271941899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1323891754572545401591 / 1000000000000000000000000 : ℝ) ≤ agent12007.charge ∧
    (374250032285934135777 / 250000000000000000000000 : ℝ) ≤ scalar12007.upperTail ∧
    (1880975051714676194359 / 1000000000000000000000000 : ℝ) ≤ scalar12007.lowerTail ∧
    scalar12007.totalBudget ≤ (849871923075453865057 / 100000000000000000000000 : ℝ) := by
  norm_num only [world12007, agent12007, scalar12007] <;> simp only [true_and]

theorem source_rounding12008 :
    (75325751017187025603 / 62500000000000000000000 : ℝ) ≤ world12008.hiddenCharge ∧
    (317885758874320658889537 / 500000000000000000000000 : ℝ) ≤ world12008.frame ∧
    (10921537657741131 / 1000000000000000000000000 : ℝ) ≤ world12008.moment ∧
    (1507526330253100521288089 / 1000000000000000000000000 : ℝ) ≤ agent12008.frame ∧
    (7595621368498740157919 / 1000000000000000000000000 : ℝ) ≤ agent12008.root ∧
    scalar12008.worldRadius ≤ (2272343199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1323512985732765798637 / 1000000000000000000000000 : ℝ) ≤ agent12008.charge ∧
    (1495632183515335632847 / 1000000000000000000000000 : ℝ) ≤ scalar12008.upperTail ∧
    (1879381216513344293207 / 1000000000000000000000000 : ℝ) ≤ scalar12008.lowerTail ∧
    scalar12008.totalBudget ≤ (849449592241260817267 / 100000000000000000000000 : ℝ) := by
  norm_num only [world12008, agent12008, scalar12008] <;> simp only [true_and]

noncomputable def paperAgent11984 : AgentParameters :=
  { agent11984 with charge := (1260365187 / 1000000000000 : ℝ) }

theorem agent_is_repriced11984 : agent11984 =
    BstLean.Part265.agentRepriced 11984 world11984 paperAgent11984 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11984, agent11984]

noncomputable def paperAgent11985 : AgentParameters :=
  { agent11985 with charge := (1260104409 / 1000000000000 : ℝ) }

theorem agent_is_repriced11985 : agent11985 =
    BstLean.Part265.agentRepriced 11985 world11985 paperAgent11985 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11985, agent11985]

noncomputable def paperAgent11986 : AgentParameters :=
  { agent11986 with charge := (125984389 / 100000000000 : ℝ) }

theorem agent_is_repriced11986 : agent11986 =
    BstLean.Part265.agentRepriced 11986 world11986 paperAgent11986 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11986, agent11986]

noncomputable def paperAgent11987 : AgentParameters :=
  { agent11987 with charge := (1259583627 / 1000000000000 : ℝ) }

theorem agent_is_repriced11987 : agent11987 =
    BstLean.Part265.agentRepriced 11987 world11987 paperAgent11987 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11987, agent11987]

noncomputable def paperAgent11988 : AgentParameters :=
  { agent11988 with charge := (1259323621 / 1000000000000 : ℝ) }

theorem agent_is_repriced11988 : agent11988 =
    BstLean.Part265.agentRepriced 11988 world11988 paperAgent11988 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11988, agent11988]

noncomputable def paperAgent11989 : AgentParameters :=
  { agent11989 with charge := (19672873 / 15625000000 : ℝ) }

theorem agent_is_repriced11989 : agent11989 =
    BstLean.Part265.agentRepriced 11989 world11989 paperAgent11989 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11989, agent11989]

noncomputable def paperAgent11990 : AgentParameters :=
  { agent11990 with charge := (1258804379 / 1000000000000 : ℝ) }

theorem agent_is_repriced11990 : agent11990 =
    BstLean.Part265.agentRepriced 11990 world11990 paperAgent11990 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11990, agent11990]

noncomputable def paperAgent11991 : AgentParameters :=
  { agent11991 with charge := (1258545143 / 1000000000000 : ℝ) }

theorem agent_is_repriced11991 : agent11991 =
    BstLean.Part265.agentRepriced 11991 world11991 paperAgent11991 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11991, agent11991]

noncomputable def paperAgent11992 : AgentParameters :=
  { agent11992 with charge := (629143081 / 500000000000 : ℝ) }

theorem agent_is_repriced11992 : agent11992 =
    BstLean.Part265.agentRepriced 11992 world11992 paperAgent11992 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11992, agent11992]

noncomputable def paperAgent11993 : AgentParameters :=
  { agent11993 with charge := (1258027437 / 1000000000000 : ℝ) }

theorem agent_is_repriced11993 : agent11993 =
    BstLean.Part265.agentRepriced 11993 world11993 paperAgent11993 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11993, agent11993]

noncomputable def paperAgent11994 : AgentParameters :=
  { agent11994 with charge := (1257768967 / 1000000000000 : ℝ) }

theorem agent_is_repriced11994 : agent11994 =
    BstLean.Part265.agentRepriced 11994 world11994 paperAgent11994 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11994, agent11994]

noncomputable def paperAgent11995 : AgentParameters :=
  { agent11995 with charge := (1257510753 / 1000000000000 : ℝ) }

theorem agent_is_repriced11995 : agent11995 =
    BstLean.Part265.agentRepriced 11995 world11995 paperAgent11995 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11995, agent11995]

noncomputable def paperAgent11996 : AgentParameters :=
  { agent11996 with charge := (157156599 / 125000000000 : ℝ) }

theorem agent_is_repriced11996 : agent11996 =
    BstLean.Part265.agentRepriced 11996 world11996 paperAgent11996 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11996, agent11996]

noncomputable def paperAgent11997 : AgentParameters :=
  { agent11997 with charge := (1256995087 / 1000000000000 : ℝ) }

theorem agent_is_repriced11997 : agent11997 =
    BstLean.Part265.agentRepriced 11997 world11997 paperAgent11997 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11997, agent11997]

noncomputable def paperAgent11998 : AgentParameters :=
  { agent11998 with charge := (251347527 / 200000000000 : ℝ) }

theorem agent_is_repriced11998 : agent11998 =
    BstLean.Part265.agentRepriced 11998 world11998 paperAgent11998 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11998, agent11998]

noncomputable def paperAgent11999 : AgentParameters :=
  { agent11999 with charge := (628240219 / 500000000000 : ℝ) }

theorem agent_is_repriced11999 : agent11999 =
    BstLean.Part265.agentRepriced 11999 world11999 paperAgent11999 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11999, agent11999]

noncomputable def paperAgent12000 : AgentParameters :=
  { agent12000 with charge := (1326556737 / 1000000000000 : ℝ) }

theorem agent_is_repriced12000 : agent12000 =
    BstLean.Part265.agentRepriced 12000 world12000 paperAgent12000 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12000, agent12000]

noncomputable def paperAgent12001 : AgentParameters :=
  { agent12001 with charge := (331543641 / 250000000000 : ℝ) }

theorem agent_is_repriced12001 : agent12001 =
    BstLean.Part265.agentRepriced 12001 world12001 paperAgent12001 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12001, agent12001]

noncomputable def paperAgent12002 : AgentParameters :=
  { agent12002 with charge := (1325792879 / 1000000000000 : ℝ) }

theorem agent_is_repriced12002 : agent12002 =
    BstLean.Part265.agentRepriced 12002 world12002 paperAgent12002 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12002, agent12002]

noncomputable def paperAgent12003 : AgentParameters :=
  { agent12003 with charge := (662705841 / 500000000000 : ℝ) }

theorem agent_is_repriced12003 : agent12003 =
    BstLean.Part265.agentRepriced 12003 world12003 paperAgent12003 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12003, agent12003]

noncomputable def paperAgent12004 : AgentParameters :=
  { agent12004 with charge := (331257743 / 250000000000 : ℝ) }

theorem agent_is_repriced12004 : agent12004 =
    BstLean.Part265.agentRepriced 12004 world12004 paperAgent12004 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12004, agent12004]

noncomputable def paperAgent12005 : AgentParameters :=
  { agent12005 with charge := (1324650749 / 1000000000000 : ℝ) }

theorem agent_is_repriced12005 : agent12005 =
    BstLean.Part265.agentRepriced 12005 world12005 paperAgent12005 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12005, agent12005]

noncomputable def paperAgent12006 : AgentParameters :=
  { agent12006 with charge := (1324271011 / 1000000000000 : ℝ) }

theorem agent_is_repriced12006 : agent12006 =
    BstLean.Part265.agentRepriced 12006 world12006 paperAgent12006 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12006, agent12006]

noncomputable def paperAgent12007 : AgentParameters :=
  { agent12007 with charge := (1323891757 / 1000000000000 : ℝ) }

theorem agent_is_repriced12007 : agent12007 =
    BstLean.Part265.agentRepriced 12007 world12007 paperAgent12007 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12007, agent12007]

noncomputable def paperAgent12008 : AgentParameters :=
  { agent12008 with charge := (1323512989 / 1000000000000 : ℝ) }

theorem agent_is_repriced12008 : agent12008 =
    BstLean.Part265.agentRepriced 12008 world12008 paperAgent12008 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent12008, agent12008]

end BstLean.Part281
