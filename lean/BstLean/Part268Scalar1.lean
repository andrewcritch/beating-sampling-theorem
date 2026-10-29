import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12375 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12375. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12375 : WorldParameters where
  hiddenCharge := (1186839077 / 1000000000000 : ℝ)
  frame := (315123215733 / 500000000000 : ℝ)
  moment := (5046948921 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12375 : AgentParameters :=
  { agentLedgerParameters with
    charge := (914187903 / 500000000000 : ℝ)
    frame := (744952220357 / 500000000000 : ℝ)
    root := (2181845947 / 250000000000 : ℝ) }

noncomputable def scalar12375 : ScalarCertificate 12375 world12375 agent12375 where
  dimensionLo := 12375
  dimensionHi := 12375
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2058736399 / 1000000000000 : ℝ)
  frameLo := (315123215733 / 500000000000 : ℝ)
  frameHi := (744952220357 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12375]
  agentFrame_pos := by norm_num only [agent12375]
  worldRadius := (2058736399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12375]
  retainedCharge := (914187903 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (970318123 / 500000000000 : ℝ)
  lowerTail := (2249410193 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4793399893 / 500000000000 : ℝ)
  ledger := by
    have h : (1186839077 / 1000000000000 : ℚ) +
        (5046948921 / 500000000000000000 : ℚ) / (2058736399 / 1000000000000 : ℚ) ^ 2 +
        (914187903 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (970318123 / 500000000000 : ℚ) + (2249410193 / 1000000000000 : ℚ) ≤
        (4793399893 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1186839077 / 1000000000000 : ℚ) +
        (5046948921 / 500000000000000000 : ℚ) / (2058736399 / 1000000000000 : ℚ) ^ 2 +
        (914187903 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (970318123 / 500000000000 : ℚ) + (2249410193 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4793399893 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12375]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12375 :
    2 * 160 < 12375 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998949 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12375 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12376 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12376. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12376 : WorldParameters where
  hiddenCharge := (1186791503 / 1000000000000 : ℝ)
  frame := (630231836291 / 1000000000000 : ℝ)
  moment := (1009176427 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12376 : AgentParameters :=
  { agentLedgerParameters with
    charge := (228460941 / 125000000000 : ℝ)
    frame := (186233511201 / 125000000000 : ℝ)
    root := (8726635651 / 1000000000000 : ℝ) }

noncomputable def scalar12376 : ScalarCertificate 12376 world12376 agent12376 where
  dimensionLo := 12376
  dimensionHi := 12376
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2059086499 / 1000000000000 : ℝ)
  frameLo := (630231836291 / 1000000000000 : ℝ)
  frameHi := (186233511201 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12376]
  agentFrame_pos := by norm_num only [agent12376]
  worldRadius := (2059086499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12376]
  retainedCharge := (228460941 / 125000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (387786369 / 200000000000 : ℝ)
  lowerTail := (2247574041 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (479060519 / 50000000000 : ℝ)
  ledger := by
    have h : (1186791503 / 1000000000000 : ℚ) +
        (1009176427 / 100000000000000000 : ℚ) / (2059086499 / 1000000000000 : ℚ) ^ 2 +
        (228460941 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (387786369 / 200000000000 : ℚ) + (2247574041 / 1000000000000 : ℚ) ≤
        (479060519 / 50000000000 : ℚ) := by norm_num only
    have hc : (((1186791503 / 1000000000000 : ℚ) +
        (1009176427 / 100000000000000000 : ℚ) / (2059086499 / 1000000000000 : ℚ) ^ 2 +
        (228460941 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (387786369 / 200000000000 : ℚ) + (2247574041 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((479060519 / 50000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12376]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12376 :
    2 * 160 < 12376 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994611 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12376 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12377 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12377. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12377 : WorldParameters where
  hiddenCharge := (593371971 / 500000000000 : ℝ)
  frame := (630217243531 / 1000000000000 : ℝ)
  moment := (315300979 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12377 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1826999867 / 1000000000000 : ℝ)
    frame := (1489831756419 / 1000000000000 : ℝ)
    root := (109073597 / 12500000000 : ℝ) }

noncomputable def scalar12377 : ScalarCertificate 12377 world12377 agent12377 where
  dimensionLo := 12377
  dimensionHi := 12377
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2059436499 / 1000000000000 : ℝ)
  frameLo := (630217243531 / 1000000000000 : ℝ)
  frameHi := (1489831756419 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12377]
  agentFrame_pos := by norm_num only [agent12377]
  worldRadius := (2059436499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12377]
  retainedCharge := (1826999867 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (7567301 / 3906250000 : ℝ)
  lowerTail := (1122869759 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1196953247 / 125000000000 : ℝ)
  ledger := by
    have h : (593371971 / 500000000000 : ℚ) +
        (315300979 / 31250000000000000 : ℚ) / (2059436499 / 1000000000000 : ℚ) ^ 2 +
        (1826999867 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (7567301 / 3906250000 : ℚ) + (1122869759 / 500000000000 : ℚ) ≤
        (1196953247 / 125000000000 : ℚ) := by norm_num only
    have hc : (((593371971 / 500000000000 : ℚ) +
        (315300979 / 31250000000000000 : ℚ) / (2059436499 / 1000000000000 : ℚ) ^ 2 +
        (1826999867 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (7567301 / 3906250000 : ℚ) + (1122869759 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1196953247 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12377]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12377 :
    2 * 160 < 12377 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999741 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12377 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12378 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12378. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12378 : WorldParameters where
  hiddenCharge := (593348197 / 500000000000 : ℝ)
  frame := (630202653187 / 1000000000000 : ℝ)
  moment := (2017499803 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12378 : AgentParameters :=
  { agentLedgerParameters with
    charge := (913156409 / 500000000000 : ℝ)
    frame := (1489795447127 / 1000000000000 : ℝ)
    root := (1745028023 / 200000000000 : ℝ) }

noncomputable def scalar12378 : ScalarCertificate 12378 world12378 agent12378 where
  dimensionLo := 12378
  dimensionHi := 12378
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2059786599 / 1000000000000 : ℝ)
  frameLo := (630202653187 / 1000000000000 : ℝ)
  frameHi := (1489795447127 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12378]
  agentFrame_pos := by norm_num only [agent12378]
  worldRadius := (2059786599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12378]
  retainedCharge := (913156409 / 500000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (483882033 / 250000000000 : ℝ)
  lowerTail := (2243906901 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2392511661 / 250000000000 : ℝ)
  ledger := by
    have h : (593348197 / 500000000000 : ℚ) +
        (2017499803 / 200000000000000000 : ℚ) / (2059786599 / 1000000000000 : ℚ) ^ 2 +
        (913156409 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (483882033 / 250000000000 : ℚ) + (2243906901 / 1000000000000 : ℚ) ≤
        (2392511661 / 250000000000 : ℚ) := by norm_num only
    have hc : (((593348197 / 500000000000 : ℚ) +
        (2017499803 / 200000000000000000 : ℚ) / (2059786599 / 1000000000000 : ℚ) ^ 2 +
        (913156409 / 500000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (483882033 / 250000000000 : ℚ) + (2243906901 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2392511661 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12378]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12378 :
    2 * 160 < 12378 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999941 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12378 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12379 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12379. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12379 : WorldParameters where
  hiddenCharge := (1186648859 / 1000000000000 : ℝ)
  frame := (630188065259 / 1000000000000 : ℝ)
  moment := (10085367333 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12379 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1825626383 / 1000000000000 : ℝ)
    frame := (1489759161717 / 1000000000000 : ℝ)
    root := (1744878543 / 200000000000 : ℝ) }

noncomputable def scalar12379 : ScalarCertificate 12379 world12379 agent12379 where
  dimensionLo := 12379
  dimensionHi := 12379
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2060136599 / 1000000000000 : ℝ)
  frameLo := (630188065259 / 1000000000000 : ℝ)
  frameHi := (1489759161717 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12379]
  agentFrame_pos := by norm_num only [agent12379]
  worldRadius := (2060136599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12379]
  retainedCharge := (1825626383 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (38676577 / 20000000000 : ℝ)
  lowerTail := (2242075949 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9564472377 / 1000000000000 : ℝ)
  ledger := by
    have h : (1186648859 / 1000000000000 : ℚ) +
        (10085367333 / 1000000000000000000 : ℚ) / (2060136599 / 1000000000000 : ℚ) ^ 2 +
        (1825626383 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (38676577 / 20000000000 : ℚ) + (2242075949 / 1000000000000 : ℚ) ≤
        (9564472377 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1186648859 / 1000000000000 : ℚ) +
        (10085367333 / 1000000000000000000 : ℚ) / (2060136599 / 1000000000000 : ℚ) ^ 2 +
        (1825626383 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (38676577 / 20000000000 : ℚ) + (2242075949 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9564472377 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12379]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12379 :
    2 * 160 < 12379 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1374999989 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12379 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12380 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12380. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12380 : WorldParameters where
  hiddenCharge := (1186601337 / 1000000000000 : ℝ)
  frame := (126034695949 / 200000000000 : ℝ)
  moment := (10083236279 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12380 : AgentParameters :=
  { agentLedgerParameters with
    charge := (22811757 / 12500000000 : ℝ)
    frame := (372409412729 / 250000000000 : ℝ)
    root := (8723645561 / 1000000000000 : ℝ) }

noncomputable def scalar12380 : ScalarCertificate 12380 world12380 agent12380 where
  dimensionLo := 12380
  dimensionHi := 12380
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2060594499 / 1000000000000 : ℝ)
  frameLo := (126034695949 / 200000000000 : ℝ)
  frameHi := (372409412729 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12380]
  agentFrame_pos := by norm_num only [agent12380]
  worldRadius := (2060594499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12380]
  retainedCharge := (22811757 / 12500000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1931775191 / 1000000000000 : ℝ)
  lowerTail := (1119898919 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9557849381 / 1000000000000 : ℝ)
  ledger := by
    have h : (1186601337 / 1000000000000 : ℚ) +
        (10083236279 / 1000000000000000000 : ℚ) / (2060594499 / 1000000000000 : ℚ) ^ 2 +
        (22811757 / 12500000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1931775191 / 1000000000000 : ℚ) + (1119898919 / 500000000000 : ℚ) ≤
        (9557849381 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1186601337 / 1000000000000 : ℚ) +
        (10083236279 / 1000000000000000000 : ℚ) / (2060594499 / 1000000000000 : ℚ) ^ 2 +
        (22811757 / 12500000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1931775191 / 1000000000000 : ℚ) + (1119898919 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9557849381 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12380]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12380 :
    2 * 160 < 12380 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999261 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12380 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12381 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12381. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12381 : WorldParameters where
  hiddenCharge := (296638457 / 250000000000 : ℝ)
  frame := (157539724161 / 250000000000 : ℝ)
  moment := (2016221171 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12381 : AgentParameters :=
  { agentLedgerParameters with
    charge := (36485107 / 20000000000 : ℝ)
    frame := (297920282857 / 200000000000 : ℝ)
    root := (2180724663 / 250000000000 : ℝ) }

noncomputable def scalar12381 : ScalarCertificate 12381 world12381 agent12381 where
  dimensionLo := 12381
  dimensionHi := 12381
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2060944599 / 1000000000000 : ℝ)
  frameLo := (157539724161 / 250000000000 : ℝ)
  frameHi := (297920282857 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12381]
  agentFrame_pos := by norm_num only [agent12381]
  worldRadius := (2060944599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12381]
  retainedCharge := (36485107 / 20000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1930079773 / 1000000000000 : ℝ)
  lowerTail := (2237970867 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9552285961 / 1000000000000 : ℝ)
  ledger := by
    have h : (296638457 / 250000000000 : ℚ) +
        (2016221171 / 200000000000000000 : ℚ) / (2060944599 / 1000000000000 : ℚ) ^ 2 +
        (36485107 / 20000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1930079773 / 1000000000000 : ℚ) + (2237970867 / 1000000000000 : ℚ) ≤
        (9552285961 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((296638457 / 250000000000 : ℚ) +
        (2016221171 / 200000000000000000 : ℚ) / (2060944599 / 1000000000000 : ℚ) ^ 2 +
        (36485107 / 20000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1930079773 / 1000000000000 : ℚ) + (2237970867 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9552285961 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12381]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12381 :
    2 * 160 < 12381 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2199999101 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12381 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12382 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12382. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12382 : WorldParameters where
  hiddenCharge := (1186506331 / 1000000000000 : ℝ)
  frame := (630144315957 / 1000000000000 : ℝ)
  moment := (10078976059 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12382 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1823570751 / 1000000000000 : ℝ)
    frame := (1489565195499 / 1000000000000 : ℝ)
    root := (2180537997 / 250000000000 : ℝ) }

noncomputable def scalar12382 : ScalarCertificate 12382 world12382 agent12382 where
  dimensionLo := 12382
  dimensionHi := 12382
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2061294799 / 1000000000000 : ℝ)
  frameLo := (630144315957 / 1000000000000 : ℝ)
  frameHi := (1489565195499 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12382]
  agentFrame_pos := by norm_num only [agent12382]
  worldRadius := (2061294799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12382]
  retainedCharge := (1823570751 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1928386179 / 1000000000000 : ℝ)
  lowerTail := (2236145753 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1909345503 / 200000000000 : ℝ)
  ledger := by
    have h : (1186506331 / 1000000000000 : ℚ) +
        (10078976059 / 1000000000000000000 : ℚ) / (2061294799 / 1000000000000 : ℚ) ^ 2 +
        (1823570751 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1928386179 / 1000000000000 : ℚ) + (2236145753 / 1000000000000 : ℚ) ≤
        (1909345503 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1186506331 / 1000000000000 : ℚ) +
        (10078976059 / 1000000000000000000 : ℚ) / (2061294799 / 1000000000000 : ℚ) ^ 2 +
        (1823570751 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1928386179 / 1000000000000 : ℚ) + (2236145753 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1909345503 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12382]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12382 :
    2 * 160 < 12382 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998431 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12382 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12383 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12383. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12383 : WorldParameters where
  hiddenCharge := (37076839 / 31250000000 : ℝ)
  frame := (630129737683 / 1000000000000 : ℝ)
  moment := (2519211723 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12383 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1822886763 / 1000000000000 : ℝ)
    frame := (1489529000537 / 1000000000000 : ℝ)
    root := (8721405641 / 1000000000000 : ℝ) }

noncomputable def scalar12383 : ScalarCertificate 12383 world12383 agent12383 where
  dimensionLo := 12383
  dimensionHi := 12383
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2061644899 / 1000000000000 : ℝ)
  frameLo := (630129737683 / 1000000000000 : ℝ)
  frameHi := (1489529000537 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12383]
  agentFrame_pos := by norm_num only [agent12383]
  worldRadius := (2061644899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12383]
  retainedCharge := (1822886763 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (240836787 / 125000000000 : ℝ)
  lowerTail := (1117161187 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9541174267 / 1000000000000 : ℝ)
  ledger := by
    have h : (37076839 / 31250000000 : ℚ) +
        (2519211723 / 250000000000000000 : ℚ) / (2061644899 / 1000000000000 : ℚ) ^ 2 +
        (1822886763 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (240836787 / 125000000000 : ℚ) + (1117161187 / 500000000000 : ℚ) ≤
        (9541174267 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((37076839 / 31250000000 : ℚ) +
        (2519211723 / 250000000000000000 : ℚ) / (2061644899 / 1000000000000 : ℚ) ^ 2 +
        (1822886763 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (240836787 / 125000000000 : ℚ) + (1117161187 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9541174267 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12383]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12383 :
    2 * 160 < 12383 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996541 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12383 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12384 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12384. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12384 : WorldParameters where
  hiddenCharge := (593205689 / 500000000000 : ℝ)
  frame := (31505758091 / 50000000000 : ℝ)
  moment := (5037359177 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12384 : AgentParameters :=
  { agentLedgerParameters with
    charge := (364440677 / 200000000000 : ℝ)
    frame := (186186603673 / 125000000000 : ℝ)
    root := (8720659467 / 1000000000000 : ℝ) }

noncomputable def scalar12384 : ScalarCertificate 12384 world12384 agent12384 where
  dimensionLo := 12384
  dimensionHi := 12384
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2061994999 / 1000000000000 : ℝ)
  frameLo := (31505758091 / 50000000000 : ℝ)
  frameHi := (186186603673 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12384]
  agentFrame_pos := by norm_num only [agent12384]
  worldRadius := (2061994999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12384]
  retainedCharge := (364440677 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (481251019 / 250000000000 : ℝ)
  lowerTail := (558125173 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4767812951 / 500000000000 : ℝ)
  ledger := by
    have h : (593205689 / 500000000000 : ℚ) +
        (5037359177 / 500000000000000000 : ℚ) / (2061994999 / 1000000000000 : ℚ) ^ 2 +
        (364440677 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (481251019 / 250000000000 : ℚ) + (558125173 / 250000000000 : ℚ) ≤
        (4767812951 / 500000000000 : ℚ) := by norm_num only
    have hc : (((593205689 / 500000000000 : ℚ) +
        (5037359177 / 500000000000000000 : ℚ) / (2061994999 / 1000000000000 : ℚ) ^ 2 +
        (364440677 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (481251019 / 250000000000 : ℚ) + (558125173 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4767812951 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12384]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12384 :
    2 * 160 < 12384 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999994511 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12384 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12385 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12385. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12385 : WorldParameters where
  hiddenCharge := (14829549 / 12500000000 : ℝ)
  frame := (630100588369 / 1000000000000 : ℝ)
  moment := (2518147611 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12385 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1821520617 / 1000000000000 : ℝ)
    frame := (1489456676033 / 1000000000000 : ℝ)
    root := (4359956769 / 500000000000 : ℝ) }

noncomputable def scalar12385 : ScalarCertificate 12385 world12385 agent12385 where
  dimensionLo := 12385
  dimensionHi := 12385
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2062345099 / 1000000000000 : ℝ)
  frameLo := (630100588369 / 1000000000000 : ℝ)
  frameHi := (1489456676033 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12385]
  agentFrame_pos := by norm_num only [agent12385]
  worldRadius := (2062345099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12385]
  retainedCharge := (1821520617 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1923315563 / 1000000000000 : ℝ)
  lowerTail := (2230680741 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4765041247 / 500000000000 : ℝ)
  ledger := by
    have h : (14829549 / 12500000000 : ℚ) +
        (2518147611 / 250000000000000000 : ℚ) / (2062345099 / 1000000000000 : ℚ) ^ 2 +
        (1821520617 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1923315563 / 1000000000000 : ℚ) + (2230680741 / 1000000000000 : ℚ) ≤
        (4765041247 / 500000000000 : ℚ) := by norm_num only
    have hc : (((14829549 / 12500000000 : ℚ) +
        (2518147611 / 250000000000000000 : ℚ) / (2062345099 / 1000000000000 : ℚ) ^ 2 +
        (1821520617 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1923315563 / 1000000000000 : ℚ) + (2230680741 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4765041247 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12385]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12385 :
    2 * 160 < 12385 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998391 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12385 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12386 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12386. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12386 : WorldParameters where
  hiddenCharge := (47452659 / 40000000000 : ℝ)
  frame := (39380376083 / 62500000000 : ℝ)
  moment := (10070463161 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12386 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1820838457 / 1000000000000 : ℝ)
    frame := (1489420546463 / 1000000000000 : ℝ)
    root := (8719167853 / 1000000000000 : ℝ) }

noncomputable def scalar12386 : ScalarCertificate 12386 world12386 agent12386 where
  dimensionLo := 12386
  dimensionHi := 12386
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2062695199 / 1000000000000 : ℝ)
  frameLo := (39380376083 / 62500000000 : ℝ)
  frameHi := (1489420546463 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12386]
  agentFrame_pos := by norm_num only [agent12386]
  worldRadius := (2062695199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12386]
  retainedCharge := (1820838457 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1921628787 / 1000000000000 : ℝ)
  lowerTail := (1114431281 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9524544113 / 1000000000000 : ℝ)
  ledger := by
    have h : (47452659 / 40000000000 : ℚ) +
        (10070463161 / 1000000000000000000 : ℚ) / (2062695199 / 1000000000000 : ℚ) ^ 2 +
        (1820838457 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1921628787 / 1000000000000 : ℚ) + (1114431281 / 500000000000 : ℚ) ≤
        (9524544113 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((47452659 / 40000000000 : ℚ) +
        (10070463161 / 1000000000000000000 : ℚ) / (2062695199 / 1000000000000 : ℚ) ^ 2 +
        (1820838457 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1921628787 / 1000000000000 : ℚ) + (1114431281 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9524544113 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12386]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12386 :
    2 * 160 < 12386 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999323 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12386 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12387 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12387. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12387 : WorldParameters where
  hiddenCharge := (1186269043 / 1000000000000 : ℝ)
  frame := (315035724349 / 500000000000 : ℝ)
  moment := (5034168253 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12387 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1820156907 / 1000000000000 : ℝ)
    frame := (1489384440659 / 1000000000000 : ℝ)
    root := (2179605603 / 250000000000 : ℝ) }

noncomputable def scalar12387 : ScalarCertificate 12387 world12387 agent12387 where
  dimensionLo := 12387
  dimensionHi := 12387
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2063045399 / 1000000000000 : ℝ)
  frameLo := (315035724349 / 500000000000 : ℝ)
  frameHi := (1489384440659 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12387]
  agentFrame_pos := by norm_num only [agent12387]
  worldRadius := (2063045399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12387]
  retainedCharge := (1820156907 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1919943857 / 1000000000000 : ℝ)
  lowerTail := (2227046269 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4759505377 / 500000000000 : ℝ)
  ledger := by
    have h : (1186269043 / 1000000000000 : ℚ) +
        (5034168253 / 500000000000000000 : ℚ) / (2063045399 / 1000000000000 : ℚ) ^ 2 +
        (1820156907 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1919943857 / 1000000000000 : ℚ) + (2227046269 / 1000000000000 : ℚ) ≤
        (4759505377 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1186269043 / 1000000000000 : ℚ) +
        (5034168253 / 500000000000000000 : ℚ) / (2063045399 / 1000000000000 : ℚ) ^ 2 +
        (1820156907 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1919943857 / 1000000000000 : ℚ) + (2227046269 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4759505377 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12387]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12387 :
    2 * 160 < 12387 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998007 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12387 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12388 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12388. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12388 : WorldParameters where
  hiddenCharge := (9489773 / 8000000000 : ℝ)
  frame := (630056882477 / 1000000000000 : ℝ)
  moment := (10066210479 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12388 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1819475963 / 1000000000000 : ℝ)
    frame := (297869670523 / 200000000000 : ℝ)
    root := (1743535443 / 200000000000 : ℝ) }

noncomputable def scalar12388 : ScalarCertificate 12388 world12388 agent12388 where
  dimensionLo := 12388
  dimensionHi := 12388
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2063395599 / 1000000000000 : ℝ)
  frameLo := (630056882477 / 1000000000000 : ℝ)
  frameHi := (297869670523 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12388]
  agentFrame_pos := by norm_num only [agent12388]
  worldRadius := (2063395599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12388]
  retainedCharge := (1819475963 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1918260627 / 1000000000000 : ℝ)
  lowerTail := (1112615851 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9513482337 / 1000000000000 : ℝ)
  ledger := by
    have h : (9489773 / 8000000000 : ℚ) +
        (10066210479 / 1000000000000000000 : ℚ) / (2063395599 / 1000000000000 : ℚ) ^ 2 +
        (1819475963 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1918260627 / 1000000000000 : ℚ) + (1112615851 / 500000000000 : ℚ) ≤
        (9513482337 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((9489773 / 8000000000 : ℚ) +
        (10066210479 / 1000000000000000000 : ℚ) / (2063395599 / 1000000000000 : ℚ) ^ 2 +
        (1819475963 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1918260627 / 1000000000000 : ℚ) + (1112615851 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9513482337 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12388]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12388 :
    2 * 160 < 12388 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999481 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12388 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12389 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12389. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12389 : WorldParameters where
  hiddenCharge := (1186174219 / 1000000000000 : ℝ)
  frame := (78755289833 / 125000000000 : ℝ)
  moment := (10064085079 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12389 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1818795627 / 1000000000000 : ℝ)
    frame := (14893122943 / 10000000000 : ℝ)
    root := (8716932263 / 1000000000000 : ℝ) }

noncomputable def scalar12389 : ScalarCertificate 12389 world12389 agent12389 where
  dimensionLo := 12389
  dimensionHi := 12389
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2063745699 / 1000000000000 : ℝ)
  frameLo := (78755289833 / 125000000000 : ℝ)
  frameHi := (14893122943 / 10000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12389]
  agentFrame_pos := by norm_num only [agent12389]
  worldRadius := (2063745699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12389]
  retainedCharge := (1818795627 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1916579051 / 1000000000000 : ℝ)
  lowerTail := (1111709411 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2376989751 / 250000000000 : ℝ)
  ledger := by
    have h : (1186174219 / 1000000000000 : ℚ) +
        (10064085079 / 1000000000000000000 : ℚ) / (2063745699 / 1000000000000 : ℚ) ^ 2 +
        (1818795627 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1916579051 / 1000000000000 : ℚ) + (1111709411 / 500000000000 : ℚ) ≤
        (2376989751 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1186174219 / 1000000000000 : ℚ) +
        (10064085079 / 1000000000000000000 : ℚ) / (2063745699 / 1000000000000 : ℚ) ^ 2 +
        (1818795627 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1916579051 / 1000000000000 : ℚ) + (1111709411 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2376989751 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12389]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12389 :
    2 * 160 < 12389 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997013 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12389 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12390 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12390. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12390 : WorldParameters where
  hiddenCharge := (47445073 / 40000000000 : ℝ)
  frame := (31501387863 / 50000000000 : ℝ)
  moment := (5030980153 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12390 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1818115899 / 1000000000000 : ℝ)
    frame := (1489191125267 / 1000000000000 : ℝ)
    root := (4358093777 / 500000000000 : ℝ) }

noncomputable def scalar12390 : ScalarCertificate 12390 world12390 agent12390 where
  dimensionLo := 12390
  dimensionHi := 12390
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2064203799 / 1000000000000 : ℝ)
  frameLo := (31501387863 / 50000000000 : ℝ)
  frameHi := (1489191125267 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12390]
  agentFrame_pos := by norm_num only [agent12390]
  worldRadius := (2064203799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12390]
  retainedCharge := (1818115899 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (239318293 / 125000000000 : ℝ)
  lowerTail := (1110581299 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1900279117 / 200000000000 : ℝ)
  ledger := by
    have h : (47445073 / 40000000000 : ℚ) +
        (5030980153 / 500000000000000000 : ℚ) / (2064203799 / 1000000000000 : ℚ) ^ 2 +
        (1818115899 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (239318293 / 125000000000 : ℚ) + (1110581299 / 500000000000 : ℚ) ≤
        (1900279117 / 200000000000 : ℚ) := by norm_num only
    have hc : (((47445073 / 40000000000 : ℚ) +
        (5030980153 / 500000000000000000 : ℚ) / (2064203799 / 1000000000000 : ℚ) ^ 2 +
        (1818115899 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (239318293 / 125000000000 : ℚ) + (1110581299 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1900279117 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12390]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12390 :
    2 * 160 < 12390 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999827 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12390 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12391 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12391. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12391 : WorldParameters where
  hiddenCharge := (237215889 / 200000000000 : ℝ)
  frame := (630013198263 / 1000000000000 : ℝ)
  moment := (7859247 / 781250000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12391 : AgentParameters :=
  { agentLedgerParameters with
    charge := (72697471 / 40000000000 : ℝ)
    frame := (372288777361 / 250000000000 : ℝ)
    root := (8715443089 / 1000000000000 : ℝ) }

noncomputable def scalar12391 : ScalarCertificate 12391 world12391 agent12391 where
  dimensionLo := 12391
  dimensionHi := 12391
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2064553999 / 1000000000000 : ℝ)
  frameLo := (630013198263 / 1000000000000 : ℝ)
  frameHi := (372288777361 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12391]
  agentFrame_pos := by norm_num only [agent12391]
  worldRadius := (2064553999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12391]
  retainedCharge := (72697471 / 40000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (956434277 / 500000000000 : ℝ)
  lowerTail := (2219353613 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2373970727 / 250000000000 : ℝ)
  ledger := by
    have h : (237215889 / 200000000000 : ℚ) +
        (7859247 / 781250000000000 : ℚ) / (2064553999 / 1000000000000 : ℚ) ^ 2 +
        (72697471 / 40000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (956434277 / 500000000000 : ℚ) + (2219353613 / 1000000000000 : ℚ) ≤
        (2373970727 / 250000000000 : ℚ) := by norm_num only
    have hc : (((237215889 / 200000000000 : ℚ) +
        (7859247 / 781250000000000 : ℚ) / (2064553999 / 1000000000000 : ℚ) ^ 2 +
        (72697471 / 40000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (956434277 / 500000000000 : ℚ) + (2219353613 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2373970727 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12391]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12391 :
    2 * 160 < 12391 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749999163 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12391 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12392 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12392. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12392 : WorldParameters where
  hiddenCharge := (593016039 / 500000000000 : ℝ)
  frame := (629998641673 / 1000000000000 : ℝ)
  moment := (1964397 / 195312500000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12392 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1816758257 / 1000000000000 : ℝ)
    frame := (372279777831 / 250000000000 : ℝ)
    root := (8714698867 / 1000000000000 : ℝ) }

noncomputable def scalar12392 : ScalarCertificate 12392 world12392 agent12392 where
  dimensionLo := 12392
  dimensionHi := 12392
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2064904099 / 1000000000000 : ℝ)
  frameLo := (629998641673 / 1000000000000 : ℝ)
  frameHi := (372279777831 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12392]
  agentFrame_pos := by norm_num only [agent12392]
  worldRadius := (2064904099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12392]
  retainedCharge := (1816758257 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (955596173 / 500000000000 : ℝ)
  lowerTail := (2217546227 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9490375151 / 1000000000000 : ℝ)
  ledger := by
    have h : (593016039 / 500000000000 : ℚ) +
        (1964397 / 195312500000000 : ℚ) / (2064904099 / 1000000000000 : ℚ) ^ 2 +
        (1816758257 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (955596173 / 500000000000 : ℚ) + (2217546227 / 1000000000000 : ℚ) ≤
        (9490375151 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((593016039 / 500000000000 : ℚ) +
        (1964397 / 195312500000000 : ℚ) / (2064904099 / 1000000000000 : ℚ) ^ 2 +
        (1816758257 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (955596173 / 500000000000 : ℚ) + (2217546227 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9490375151 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12392]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12392 :
    2 * 160 < 12392 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999998121 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12392 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12393 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12393. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12393 : WorldParameters where
  hiddenCharge := (1185984723 / 1000000000000 : ℝ)
  frame := (62998408749 / 100000000000 : ℝ)
  moment := (5027794873 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12393 : AgentParameters :=
  { agentLedgerParameters with
    charge := (227010043 / 125000000000 : ℝ)
    frame := (372270784221 / 250000000000 : ℝ)
    root := (8713954889 / 1000000000000 : ℝ) }

noncomputable def scalar12393 : ScalarCertificate 12393 world12393 agent12393 where
  dimensionLo := 12393
  dimensionHi := 12393
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2065254299 / 1000000000000 : ℝ)
  frameLo := (62998408749 / 100000000000 : ℝ)
  frameHi := (372270784221 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12393]
  agentFrame_pos := by norm_num only [agent12393]
  worldRadius := (2065254299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12393]
  retainedCharge := (227010043 / 125000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (190951797 / 100000000000 : ℝ)
  lowerTail := (553935179 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4742436191 / 500000000000 : ℝ)
  ledger := by
    have h : (1185984723 / 1000000000000 : ℚ) +
        (5027794873 / 500000000000000000 : ℚ) / (2065254299 / 1000000000000 : ℚ) ^ 2 +
        (227010043 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (190951797 / 100000000000 : ℚ) + (553935179 / 250000000000 : ℚ) ≤
        (4742436191 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1185984723 / 1000000000000 : ℚ) +
        (5027794873 / 500000000000000000 : ℚ) / (2065254299 / 1000000000000 : ℚ) ^ 2 +
        (227010043 / 125000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (190951797 / 100000000000 : ℚ) + (553935179 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4742436191 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12393]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12393 :
    2 * 160 < 12393 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499998821 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12393 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12394 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12394. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12394 : WorldParameters where
  hiddenCharge := (1185937381 / 1000000000000 : ℝ)
  frame := (19686547991 / 31250000000 : ℝ)
  moment := (10053467479 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12394 : AgentParameters :=
  { agentLedgerParameters with
    charge := (363080607 / 200000000000 : ℝ)
    frame := (148904718611 / 100000000000 : ℝ)
    root := (4356605577 / 500000000000 : ℝ) }

noncomputable def scalar12394 : ScalarCertificate 12394 world12394 agent12394 where
  dimensionLo := 12394
  dimensionHi := 12394
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2065604499 / 1000000000000 : ℝ)
  frameLo := (19686547991 / 31250000000 : ℝ)
  frameHi := (148904718611 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12394]
  agentFrame_pos := by norm_num only [agent12394]
  worldRadius := (2065604499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12394]
  retainedCharge := (363080607 / 200000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (476961329 / 250000000000 : ℝ)
  lowerTail := (1106968479 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (2369843649 / 250000000000 : ℝ)
  ledger := by
    have h : (1185937381 / 1000000000000 : ℚ) +
        (10053467479 / 1000000000000000000 : ℚ) / (2065604499 / 1000000000000 : ℚ) ^ 2 +
        (363080607 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (476961329 / 250000000000 : ℚ) + (1106968479 / 500000000000 : ℚ) ≤
        (2369843649 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1185937381 / 1000000000000 : ℚ) +
        (10053467479 / 1000000000000000000 : ℚ) / (2065604499 / 1000000000000 : ℚ) ^ 2 +
        (363080607 / 200000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (476961329 / 250000000000 : ℚ) + (1106968479 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((2369843649 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12394]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12394 :
    2 * 160 < 12394 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998797 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12394 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12395 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12395. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12395 : WorldParameters where
  hiddenCharge := (1185890053 / 1000000000000 : ℝ)
  frame := (629954986339 / 1000000000000 : ℝ)
  moment := (10051345837 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12395 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1814726329 / 1000000000000 : ℝ)
    frame := (372252813249 / 250000000000 : ℝ)
    root := (8712467661 / 1000000000000 : ℝ) }

noncomputable def scalar12395 : ScalarCertificate 12395 world12395 agent12395 where
  dimensionLo := 12395
  dimensionHi := 12395
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2065954699 / 1000000000000 : ℝ)
  frameLo := (629954986339 / 1000000000000 : ℝ)
  frameHi := (372252813249 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12395]
  agentFrame_pos := by norm_num only [agent12395]
  worldRadius := (2065954699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12395]
  retainedCharge := (1814726329 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1906174347 / 1000000000000 : ℝ)
  lowerTail := (2212134913 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (4736940857 / 500000000000 : ℝ)
  ledger := by
    have h : (1185890053 / 1000000000000 : ℚ) +
        (10051345837 / 1000000000000000000 : ℚ) / (2065954699 / 1000000000000 : ℚ) ^ 2 +
        (1814726329 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1906174347 / 1000000000000 : ℚ) + (2212134913 / 1000000000000 : ℚ) ≤
        (4736940857 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1185890053 / 1000000000000 : ℚ) +
        (10051345837 / 1000000000000000000 : ℚ) / (2065954699 / 1000000000000 : ℚ) ^ 2 +
        (1814726329 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1906174347 / 1000000000000 : ℚ) + (2212134913 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((4736940857 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12395]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12395 :
    2 * 160 < 12395 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (10999996787 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12395 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12396 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12396. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12396 : WorldParameters where
  hiddenCharge := (1185842737 / 1000000000000 : ℝ)
  frame := (62994043937 / 100000000000 : ℝ)
  moment := (10049224821 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12396 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1814050227 / 1000000000000 : ℝ)
    frame := (1488975343521 / 1000000000000 : ℝ)
    root := (2177931103 / 250000000000 : ℝ) }

noncomputable def scalar12396 : ScalarCertificate 12396 world12396 agent12396 where
  dimensionLo := 12396
  dimensionHi := 12396
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2066304799 / 1000000000000 : ℝ)
  frameLo := (62994043937 / 100000000000 : ℝ)
  frameHi := (1488975343521 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12396]
  agentFrame_pos := by norm_num only [agent12396]
  worldRadius := (2066304799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12396]
  retainedCharge := (1814050227 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (380900997 / 200000000000 : ℝ)
  lowerTail := (4420669 / 2000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1893678761 / 200000000000 : ℝ)
  ledger := by
    have h : (1185842737 / 1000000000000 : ℚ) +
        (10049224821 / 1000000000000000000 : ℚ) / (2066304799 / 1000000000000 : ℚ) ^ 2 +
        (1814050227 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (380900997 / 200000000000 : ℚ) + (4420669 / 2000000000 : ℚ) ≤
        (1893678761 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1185842737 / 1000000000000 : ℚ) +
        (10049224821 / 1000000000000000000 : ℚ) / (2066304799 / 1000000000000 : ℚ) ^ 2 +
        (1814050227 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (380900997 / 200000000000 : ℚ) + (4420669 / 2000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1893678761 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12396]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12396 :
    2 * 160 < 12396 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (274999909 / 25000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12396 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12397 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12397. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12397 : WorldParameters where
  hiddenCharge := (1185795433 / 1000000000000 : ℝ)
  frame := (125985178961 / 200000000000 : ℝ)
  moment := (1004710443 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12397 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1813374727 / 1000000000000 : ℝ)
    frame := (744469725839 / 500000000000 : ℝ)
    root := (1742196281 / 200000000000 : ℝ) }

noncomputable def scalar12397 : ScalarCertificate 12397 world12397 agent12397 where
  dimensionLo := 12397
  dimensionHi := 12397
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2066655099 / 1000000000000 : ℝ)
  frameLo := (125985178961 / 200000000000 : ℝ)
  frameHi := (744469725839 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12397]
  agentFrame_pos := by norm_num only [agent12397]
  worldRadius := (2066655099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12397]
  retainedCharge := (1813374727 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (475709381 / 250000000000 : ℝ)
  lowerTail := (2208536031 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9462910789 / 1000000000000 : ℝ)
  ledger := by
    have h : (1185795433 / 1000000000000 : ℚ) +
        (1004710443 / 100000000000000000 : ℚ) / (2066655099 / 1000000000000 : ℚ) ^ 2 +
        (1813374727 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (475709381 / 250000000000 : ℚ) + (2208536031 / 1000000000000 : ℚ) ≤
        (9462910789 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1185795433 / 1000000000000 : ℚ) +
        (1004710443 / 100000000000000000 : ℚ) / (2066655099 / 1000000000000 : ℚ) ^ 2 +
        (1813374727 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (475709381 / 250000000000 : ℚ) + (2208536031 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9462910789 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12397]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12397 :
    2 * 160 < 12397 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499999969 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12397 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12398 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12398. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12398 : WorldParameters where
  hiddenCharge := (1185748143 / 1000000000000 : ℝ)
  frame := (314955676321 / 500000000000 : ℝ)
  moment := (1255623083 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12398 : AgentParameters :=
  { agentLedgerParameters with
    charge := (1812699829 / 1000000000000 : ℝ)
    frame := (297780717887 / 200000000000 : ℝ)
    root := (8710238641 / 1000000000000 : ℝ) }

noncomputable def scalar12398 : ScalarCertificate 12398 world12398 agent12398 where
  dimensionLo := 12398
  dimensionHi := 12398
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2067005199 / 1000000000000 : ℝ)
  frameLo := (314955676321 / 500000000000 : ℝ)
  frameHi := (297780717887 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12398]
  agentFrame_pos := by norm_num only [agent12398]
  worldRadius := (2067005199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12398]
  retainedCharge := (1812699829 / 1000000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1901171589 / 1000000000000 : ℝ)
  lowerTail := (275842389 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1182179101 / 125000000000 : ℝ)
  ledger := by
    have h : (1185748143 / 1000000000000 : ℚ) +
        (1255623083 / 125000000000000000 : ℚ) / (2067005199 / 1000000000000 : ℚ) ^ 2 +
        (1812699829 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1901171589 / 1000000000000 : ℚ) + (275842389 / 125000000000 : ℚ) ≤
        (1182179101 / 125000000000 : ℚ) := by norm_num only
    have hc : (((1185748143 / 1000000000000 : ℚ) +
        (1255623083 / 125000000000000000 : ℚ) / (2067005199 / 1000000000000 : ℚ) ^ 2 +
        (1812699829 / 1000000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1901171589 / 1000000000000 : ℚ) + (275842389 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1182179101 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12398]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12398 :
    2 * 160 < 12398 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (5499997689 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12398 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12399 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12399. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12399 : WorldParameters where
  hiddenCharge := (592850433 / 500000000000 : ℝ)
  frame := (629896812883 / 1000000000000 : ℝ)
  moment := (10042865523 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12399 : AgentParameters :=
  { agentLedgerParameters with
    charge := (453006383 / 250000000000 : ℝ)
    frame := (1488867744797 / 1000000000000 : ℝ)
    root := (8709496119 / 1000000000000 : ℝ) }

noncomputable def scalar12399 : ScalarCertificate 12399 world12399 agent12399 where
  dimensionLo := 12399
  dimensionHi := 12399
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2067355499 / 1000000000000 : ℝ)
  frameLo := (629896812883 / 1000000000000 : ℝ)
  frameHi := (1488867744797 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12399]
  agentFrame_pos := by norm_num only [agent12399]
  worldRadius := (2067355499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12399]
  retainedCharge := (453006383 / 250000000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (59359611 / 31250000000 : ℝ)
  lowerTail := (2204944133 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (9451959709 / 1000000000000 : ℝ)
  ledger := by
    have h : (592850433 / 500000000000 : ℚ) +
        (10042865523 / 1000000000000000000 : ℚ) / (2067355499 / 1000000000000 : ℚ) ^ 2 +
        (453006383 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (59359611 / 31250000000 : ℚ) + (2204944133 / 1000000000000 : ℚ) ≤
        (9451959709 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((592850433 / 500000000000 : ℚ) +
        (10042865523 / 1000000000000000000 : ℚ) / (2067355499 / 1000000000000 : ℚ) ^ 2 +
        (453006383 / 250000000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (59359611 / 31250000000 : ℚ) + (2204944133 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((9451959709 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12399]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12399 :
    2 * 160 < 12399 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2749998693 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12399 {← IO.monoMsNow}" : IO Unit)
