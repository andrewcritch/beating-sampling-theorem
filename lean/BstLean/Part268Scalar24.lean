import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12950 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12950. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12950 : WorldParameters where
  hiddenCharge := (1161482333 / 1000000000000 : ℝ)
  frame := (311116924697 / 500000000000 : ℝ)
  moment := (8964012773 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12950 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (293270908933 / 200000000000 : ℝ)
    root := (8331164347 / 1000000000000 : ℝ) }

noncomputable def scalar12950 : ScalarCertificate 12950 world12950 agent12950 where
  dimensionLo := 12950
  dimensionHi := 12950
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2269862499 / 1000000000000 : ℝ)
  frameLo := (311116924697 / 500000000000 : ℝ)
  frameHi := (293270908933 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12950]
  agentFrame_pos := by norm_num only [agent12950]
  worldRadius := (2269862499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12950]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (47110243 / 40000000000 : ℝ)
  lowerTail := (141218431 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7290384899 / 1000000000000 : ℝ)
  ledger := by
    have h : (1161482333 / 1000000000000 : ℚ) +
        (8964012773 / 1000000000000000000 : ℚ) / (2269862499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (47110243 / 40000000000 : ℚ) + (141218431 / 100000000000 : ℚ) ≤
        (7290384899 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1161482333 / 1000000000000 : ℚ) +
        (8964012773 / 1000000000000000000 : ℚ) / (2269862499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (47110243 / 40000000000 : ℚ) + (141218431 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7290384899 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12950]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12950 :
    2 * 160 < 12950 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999107 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12950 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12951 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12951. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12951 : WorldParameters where
  hiddenCharge := (145180187 / 125000000000 : ℝ)
  frame := (311110272589 / 500000000000 : ℝ)
  moment := (70017229 / 7812500000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12951 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1466324817921 / 1000000000000 : ℝ)
    root := (833053089 / 100000000000 : ℝ) }

noncomputable def scalar12951 : ScalarCertificate 12951 world12951 agent12951 where
  dimensionLo := 12951
  dimensionHi := 12951
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2270223999 / 1000000000000 : ℝ)
  frameLo := (311110272589 / 500000000000 : ℝ)
  frameHi := (1466324817921 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12951]
  agentFrame_pos := by norm_num only [agent12951]
  worldRadius := (2270223999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12951]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1176787287 / 1000000000000 : ℝ)
  lowerTail := (1411105817 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (455462003 / 62500000000 : ℝ)
  ledger := by
    have h : (145180187 / 125000000000 : ℚ) +
        (70017229 / 7812500000000000 : ℚ) / (2270223999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1176787287 / 1000000000000 : ℚ) + (1411105817 / 1000000000000 : ℚ) ≤
        (455462003 / 62500000000 : ℚ) := by norm_num only
    have hc : (((145180187 / 125000000000 : ℚ) +
        (70017229 / 7812500000000000 : ℚ) / (2270223999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1176787287 / 1000000000000 : ℚ) + (1411105817 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((455462003 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12951]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12951 :
    2 * 160 < 12951 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999031 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12951 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12952 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12952. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12952 : WorldParameters where
  hiddenCharge := (1161400671 / 1000000000000 : ℝ)
  frame := (622207243047 / 1000000000000 : ℝ)
  moment := (224009959 / 25000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12952 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1466295103467 / 1000000000000 : ℝ)
    root := (8329897613 / 1000000000000 : ℝ) }

noncomputable def scalar12952 : ScalarCertificate 12952 world12952 agent12952 where
  dimensionLo := 12952
  dimensionHi := 12952
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2270585599 / 1000000000000 : ℝ)
  frameLo := (622207243047 / 1000000000000 : ℝ)
  frameHi := (1466295103467 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12952]
  agentFrame_pos := by norm_num only [agent12952]
  worldRadius := (2270585599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12952]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1175819479 / 1000000000000 : ℝ)
  lowerTail := (352507089 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7284401653 / 1000000000000 : ℝ)
  ledger := by
    have h : (1161400671 / 1000000000000 : ℚ) +
        (224009959 / 25000000000000000 : ℚ) / (2270585599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1175819479 / 1000000000000 : ℚ) + (352507089 / 250000000000 : ℚ) ≤
        (7284401653 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1161400671 / 1000000000000 : ℚ) +
        (224009959 / 25000000000000000 : ℚ) / (2270585599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1175819479 / 1000000000000 : ℚ) + (352507089 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7284401653 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12952]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12952 :
    2 * 160 < 12952 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999493 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12952 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12953 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12953. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12953 : WorldParameters where
  hiddenCharge := (72584991 / 62500000000 : ℝ)
  frame := (622193943 / 1000000000 : ℝ)
  moment := (4479295959 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12953 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1466265407163 / 1000000000000 : ℝ)
    root := (4164632259 / 500000000000 : ℝ) }

noncomputable def scalar12953 : ScalarCertificate 12953 world12953 agent12953 where
  dimensionLo := 12953
  dimensionHi := 12953
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2270947099 / 1000000000000 : ℝ)
  frameLo := (622193943 / 1000000000 : ℝ)
  frameHi := (1466265407163 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12953]
  agentFrame_pos := by norm_num only [agent12953]
  worldRadius := (2270947099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12953]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1174852529 / 1000000000000 : ℝ)
  lowerTail := (88059487 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3640706883 / 500000000000 : ℝ)
  ledger := by
    have h : (72584991 / 62500000000 : ℚ) +
        (4479295959 / 500000000000000000 : ℚ) / (2270947099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1174852529 / 1000000000000 : ℚ) + (88059487 / 62500000000 : ℚ) ≤
        (3640706883 / 500000000000 : ℚ) := by norm_num only
    have hc : (((72584991 / 62500000000 : ℚ) +
        (4479295959 / 500000000000000000 : ℚ) / (2270947099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1174852529 / 1000000000000 : ℚ) + (88059487 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((3640706883 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12953]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12953 :
    2 * 160 < 12953 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (399999999 / 40000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12953 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12954 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12954. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12954 : WorldParameters where
  hiddenCharge := (1161319051 / 1000000000000 : ℝ)
  frame := (155545161259 / 250000000000 : ℝ)
  moment := (139949781 / 15625000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12954 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733117864501 / 500000000000 : ℝ)
    root := (8328631667 / 1000000000000 : ℝ) }

noncomputable def scalar12954 : ScalarCertificate 12954 world12954 agent12954 where
  dimensionLo := 12954
  dimensionHi := 12954
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2271308599 / 1000000000000 : ℝ)
  frameLo := (155545161259 / 250000000000 : ℝ)
  frameHi := (733117864501 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12954]
  agentFrame_pos := by norm_num only [agent12954]
  worldRadius := (2271308599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12954]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (586943277 / 500000000000 : ℝ)
  lowerTail := (351969063 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7278428471 / 1000000000000 : ℝ)
  ledger := by
    have h : (1161319051 / 1000000000000 : ℚ) +
        (139949781 / 15625000000000000 : ℚ) / (2271308599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (586943277 / 500000000000 : ℚ) + (351969063 / 250000000000 : ℚ) ≤
        (7278428471 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1161319051 / 1000000000000 : ℚ) +
        (139949781 / 15625000000000000 : ℚ) / (2271308599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (586943277 / 500000000000 : ℚ) + (351969063 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7278428471 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12954]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12954 :
    2 * 160 < 12954 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997547 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12954 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12955 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12955. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12955 : WorldParameters where
  hiddenCharge := (580639129 / 500000000000 : ℝ)
  frame := (124433469831 / 200000000000 : ℝ)
  moment := (8954980559 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12955 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1466206063109 / 1000000000000 : ℝ)
    root := (4163999467 / 500000000000 : ℝ) }

noncomputable def scalar12955 : ScalarCertificate 12955 world12955 agent12955 where
  dimensionLo := 12955
  dimensionHi := 12955
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2271670099 / 1000000000000 : ℝ)
  frameLo := (124433469831 / 200000000000 : ℝ)
  frameHi := (1466206063109 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12955]
  agentFrame_pos := by norm_num only [agent12955]
  worldRadius := (2271670099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12955]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (586460719 / 500000000000 : ℝ)
  lowerTail := (281360323 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (227357673 / 31250000000 : ℝ)
  ledger := by
    have h : (580639129 / 500000000000 : ℚ) +
        (8954980559 / 1000000000000000000 : ℚ) / (2271670099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (586460719 / 500000000000 : ℚ) + (281360323 / 200000000000 : ℚ) ≤
        (227357673 / 31250000000 : ℚ) := by norm_num only
    have hc : (((580639129 / 500000000000 : ℚ) +
        (8954980559 / 1000000000000000000 : ℚ) / (2271670099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (586460719 / 500000000000 : ℚ) + (281360323 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((227357673 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12955]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12955 :
    2 * 160 < 12955 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998919 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12955 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12956 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12956. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12956 : WorldParameters where
  hiddenCharge := (580618737 / 500000000000 : ℝ)
  frame := (155538513839 / 250000000000 : ℝ)
  moment := (4476587821 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12956 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (293235283069 / 200000000000 : ℝ)
    root := (8327366381 / 1000000000000 : ℝ) }

noncomputable def scalar12956 : ScalarCertificate 12956 world12956 agent12956 where
  dimensionLo := 12956
  dimensionHi := 12956
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2272031699 / 1000000000000 : ℝ)
  frameLo := (155538513839 / 250000000000 : ℝ)
  frameHi := (293235283069 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12956]
  agentFrame_pos := by norm_num only [agent12956]
  worldRadius := (2272031699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12956]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (585978661 / 500000000000 : ℝ)
  lowerTail := (1405728033 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3636232549 / 500000000000 : ℝ)
  ledger := by
    have h : (580618737 / 500000000000 : ℚ) +
        (4476587821 / 500000000000000000 : ℚ) / (2272031699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (585978661 / 500000000000 : ℚ) + (1405728033 / 1000000000000 : ℚ) ≤
        (3636232549 / 500000000000 : ℚ) := by norm_num only
    have hc : (((580618737 / 500000000000 : ℚ) +
        (4476587821 / 500000000000000000 : ℚ) / (2272031699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (585978661 / 500000000000 : ℚ) + (1405728033 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3636232549 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12956]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12956 :
    2 * 160 < 12956 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995177 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12956 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12957 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12957. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12957 : WorldParameters where
  hiddenCharge := (580598351 / 500000000000 : ℝ)
  frame := (15553519091 / 25000000000 : ℝ)
  moment := (4475685617 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12957 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (366536694959 / 250000000000 : ℝ)
    root := (1040841751 / 125000000000 : ℝ) }

noncomputable def scalar12957 : ScalarCertificate 12957 world12957 agent12957 where
  dimensionLo := 12957
  dimensionHi := 12957
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2272393299 / 1000000000000 : ℝ)
  frameLo := (15553519091 / 25000000000 : ℝ)
  frameHi := (366536694959 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12957]
  agentFrame_pos := by norm_num only [agent12957]
  worldRadius := (2272393299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12957]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (117099411 / 100000000000 : ℝ)
  lowerTail := (1404655397 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1453897421 / 200000000000 : ℝ)
  ledger := by
    have h : (580598351 / 500000000000 : ℚ) +
        (4475685617 / 500000000000000000 : ℚ) / (2272393299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (117099411 / 100000000000 : ℚ) + (1404655397 / 1000000000000 : ℚ) ≤
        (1453897421 / 200000000000 : ℚ) := by norm_num only
    have hc : (((580598351 / 500000000000 : ℚ) +
        (4475685617 / 500000000000000000 : ℚ) / (2272393299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (117099411 / 100000000000 : ℚ) + (1404655397 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1453897421 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12957]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12957 :
    2 * 160 < 12957 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999039 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12957 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12958 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12958. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12958 : WorldParameters where
  hiddenCharge := (58057797 / 50000000000 : ℝ)
  frame := (155531868501 / 250000000000 : ℝ)
  moment := (8949567333 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12958 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (733058578287 / 500000000000 : ℝ)
    root := (208152547 / 25000000000 : ℝ) }

noncomputable def scalar12958 : ScalarCertificate 12958 world12958 agent12958 where
  dimensionLo := 12958
  dimensionHi := 12958
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2272754699 / 1000000000000 : ℝ)
  frameLo := (155531868501 / 250000000000 : ℝ)
  frameHi := (733058578287 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12958]
  agentFrame_pos := by norm_num only [agent12958]
  worldRadius := (2272754699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12958]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (585015851 / 500000000000 : ℝ)
  lowerTail := (1403583593 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (227078489 / 31250000000 : ℝ)
  ledger := by
    have h : (58057797 / 50000000000 : ℚ) +
        (8949567333 / 1000000000000000000 : ℚ) / (2272754699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (585015851 / 500000000000 : ℚ) + (1403583593 / 1000000000000 : ℚ) ≤
        (227078489 / 31250000000 : ℚ) := by norm_num only
    have hc : (((58057797 / 50000000000 : ℚ) +
        (8949567333 / 1000000000000000000 : ℚ) / (2272754699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (585015851 / 500000000000 : ℚ) + (1403583593 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((227078489 / 31250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12958]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12958 :
    2 * 160 < 12958 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (79999983 / 8000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12958 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12959 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12959. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12959 : WorldParameters where
  hiddenCharge := (290278797 / 250000000000 : ℝ)
  frame := (12442283729 / 20000000000 : ℝ)
  moment := (8947763941 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12959 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1466087551419 / 1000000000000 : ℝ)
    root := (2081367467 / 250000000000 : ℝ) }

noncomputable def scalar12959 : ScalarCertificate 12959 world12959 agent12959 where
  dimensionLo := 12959
  dimensionHi := 12959
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2273116299 / 1000000000000 : ℝ)
  frameLo := (12442283729 / 20000000000 : ℝ)
  frameHi := (1466087551419 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12959]
  agentFrame_pos := by norm_num only [agent12959]
  worldRadius := (2273116299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12959]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (292267579 / 250000000000 : ℝ)
  lowerTail := (350628219 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1815884647 / 250000000000 : ℝ)
  ledger := by
    have h : (290278797 / 250000000000 : ℚ) +
        (8947763941 / 1000000000000000000 : ℚ) / (2273116299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (292267579 / 250000000000 : ℚ) + (350628219 / 250000000000 : ℚ) ≤
        (1815884647 / 250000000000 : ℚ) := by norm_num only
    have hc : (((290278797 / 250000000000 : ℚ) +
        (8947763941 / 1000000000000000000 : ℚ) / (2273116299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (292267579 / 250000000000 : ℚ) + (350628219 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1815884647 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12959]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12959 :
    2 * 160 < 12959 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997541 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12959 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12960 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12960. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12960 : WorldParameters where
  hiddenCharge := (1161074447 / 1000000000000 : ℝ)
  frame := (38881306311 / 62500000000 : ℝ)
  moment := (8945961057 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12960 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1465979535693 / 1000000000000 : ℝ)
    root := (8324838037 / 1000000000000 : ℝ) }

noncomputable def scalar12960 : ScalarCertificate 12960 world12960 agent12960 where
  dimensionLo := 12960
  dimensionHi := 12960
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2273593699 / 1000000000000 : ℝ)
  frameLo := (38881306311 / 62500000000 : ℝ)
  frameHi := (1465979535693 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12960]
  agentFrame_pos := by norm_num only [agent12960]
  worldRadius := (2273593699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12960]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (116790283 / 100000000000 : ℝ)
  lowerTail := (87573257 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3629956837 / 500000000000 : ℝ)
  ledger := by
    have h : (1161074447 / 1000000000000 : ℚ) +
        (8945961057 / 1000000000000000000 : ℚ) / (2273593699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (116790283 / 100000000000 : ℚ) + (87573257 / 62500000000 : ℚ) ≤
        (3629956837 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1161074447 / 1000000000000 : ℚ) +
        (8945961057 / 1000000000000000000 : ℚ) / (2273593699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (116790283 / 100000000000 : ℚ) + (87573257 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((3629956837 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12960]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12960 :
    2 * 160 < 12960 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999829 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12960 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12961 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12961. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12961 : WorldParameters where
  hiddenCharge := (1161033717 / 1000000000000 : ℝ)
  frame := (311043808791 / 500000000000 : ℝ)
  moment := (223603967 / 25000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12961 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1465949961749 / 1000000000000 : ℝ)
    root := (4162103193 / 500000000000 : ℝ) }

noncomputable def scalar12961 : ScalarCertificate 12961 world12961 agent12961 where
  dimensionLo := 12961
  dimensionHi := 12961
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2273955299 / 1000000000000 : ℝ)
  frameLo := (311043808791 / 500000000000 : ℝ)
  frameHi := (1465949961749 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12961]
  agentFrame_pos := by norm_num only [agent12961]
  worldRadius := (2273955299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12961]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1166943409 / 1000000000000 : ℝ)
  lowerTail := (1400103479 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (725694597 / 100000000000 : ℝ)
  ledger := by
    have h : (1161033717 / 1000000000000 : ℚ) +
        (223603967 / 25000000000000000 : ℚ) / (2273955299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1166943409 / 1000000000000 : ℚ) + (1400103479 / 1000000000000 : ℚ) ≤
        (725694597 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1161033717 / 1000000000000 : ℚ) +
        (223603967 / 25000000000000000 : ℚ) / (2273955299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1166943409 / 1000000000000 : ℚ) + (1400103479 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((725694597 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12961]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12961 :
    2 * 160 < 12961 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999531 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12961 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12962 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12962. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12962 : WorldParameters where
  hiddenCharge := (1160992997 / 1000000000000 : ℝ)
  frame := (622074336267 / 1000000000000 : ℝ)
  moment := (8942356811 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12962 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1465920405889 / 1000000000000 : ℝ)
    root := (4161787489 / 500000000000 : ℝ) }

noncomputable def scalar12962 : ScalarCertificate 12962 world12962 agent12962 where
  dimensionLo := 12962
  dimensionHi := 12962
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2274316899 / 1000000000000 : ℝ)
  frameLo := (622074336267 / 1000000000000 : ℝ)
  frameHi := (1465920405889 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12962]
  agentFrame_pos := by norm_num only [agent12962]
  worldRadius := (2274316899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12962]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1165984953 / 1000000000000 : ℝ)
  lowerTail := (1399035861 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7253980841 / 1000000000000 : ℝ)
  ledger := by
    have h : (1160992997 / 1000000000000 : ℚ) +
        (8942356811 / 1000000000000000000 : ℚ) / (2274316899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1165984953 / 1000000000000 : ℚ) + (1399035861 / 1000000000000 : ℚ) ≤
        (7253980841 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1160992997 / 1000000000000 : ℚ) +
        (8942356811 / 1000000000000000000 : ℚ) / (2274316899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1165984953 / 1000000000000 : ℚ) + (1399035861 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7253980841 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12962]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12962 :
    2 * 160 < 12962 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (624999701 / 62500000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12962 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12963 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12963. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12963 : WorldParameters where
  hiddenCharge := (36279759 / 31250000000 : ℝ)
  frame := (62206105703 / 100000000000 : ℝ)
  moment := (1117569431 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12963 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183236357047 / 125000000000 : ℝ)
    root := (8322943687 / 1000000000000 : ℝ) }

noncomputable def scalar12963 : ScalarCertificate 12963 world12963 agent12963 where
  dimensionLo := 12963
  dimensionHi := 12963
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2274678499 / 1000000000000 : ℝ)
  frameLo := (62206105703 / 100000000000 : ℝ)
  frameHi := (183236357047 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12963]
  agentFrame_pos := by norm_num only [agent12963]
  worldRadius := (2274678499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12963]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (568861 / 488281250 : ℝ)
  lowerTail := (139796911 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3625509 / 500000000 : ℝ)
  ledger := by
    have h : (36279759 / 31250000000 : ℚ) +
        (1117569431 / 125000000000000000 : ℚ) / (2274678499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (568861 / 488281250 : ℚ) + (139796911 / 100000000000 : ℚ) ≤
        (3625509 / 500000000 : ℚ) := by norm_num only
    have hc : (((36279759 / 31250000000 : ℚ) +
        (1117569431 / 125000000000000000 : ℚ) / (2274678499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (568861 / 488281250 : ℚ) + (139796911 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3625509 / 500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12963]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12963 :
    2 * 160 < 12963 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999599 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12963 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12964 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12964. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12964 : WorldParameters where
  hiddenCharge := (1160911589 / 1000000000000 : ℝ)
  frame := (19438993121 / 31250000000 : ℝ)
  moment := (8938754593 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12964 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (732930665399 / 500000000000 : ℝ)
    root := (65018067 / 7812500000 : ℝ) }

noncomputable def scalar12964 : ScalarCertificate 12964 world12964 agent12964 where
  dimensionLo := 12964
  dimensionHi := 12964
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2275040099 / 1000000000000 : ℝ)
  frameLo := (19438993121 / 31250000000 : ℝ)
  frameHi := (732930665399 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12964]
  agentFrame_pos := by norm_num only [agent12964]
  worldRadius := (2275040099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12964]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (291017661 / 250000000000 : ℝ)
  lowerTail := (1396903353 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7248057687 / 1000000000000 : ℝ)
  ledger := by
    have h : (1160911589 / 1000000000000 : ℚ) +
        (8938754593 / 1000000000000000000 : ℚ) / (2275040099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (291017661 / 250000000000 : ℚ) + (1396903353 / 1000000000000 : ℚ) ≤
        (7248057687 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1160911589 / 1000000000000 : ℚ) +
        (8938754593 / 1000000000000000000 : ℚ) / (2275040099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (291017661 / 250000000000 : ℚ) + (1396903353 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7248057687 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12964]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12964 :
    2 * 160 < 12964 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995197 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12964 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12965 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12965. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12965 : WorldParameters where
  hiddenCharge := (1160870901 / 1000000000000 : ℝ)
  frame := (77754313099 / 125000000000 : ℝ)
  moment := (1787390849 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12965 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (732915905777 / 500000000000 : ℝ)
    root := (2080420411 / 250000000000 : ℝ) }

noncomputable def scalar12965 : ScalarCertificate 12965 world12965 agent12965 where
  dimensionLo := 12965
  dimensionHi := 12965
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2275401799 / 1000000000000 : ℝ)
  frameLo := (77754313099 / 125000000000 : ℝ)
  frameHi := (732915905777 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12965]
  agentFrame_pos := by norm_num only [agent12965]
  worldRadius := (2275401799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12965]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (232622981 / 200000000000 : ℝ)
  lowerTail := (348959647 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7245099751 / 1000000000000 : ℝ)
  ledger := by
    have h : (1160870901 / 1000000000000 : ℚ) +
        (1787390849 / 200000000000000000 : ℚ) / (2275401799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (232622981 / 200000000000 : ℚ) + (348959647 / 250000000000 : ℚ) ≤
        (7245099751 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1160870901 / 1000000000000 : ℚ) +
        (1787390849 / 200000000000000000 : ℚ) / (2275401799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (232622981 / 200000000000 : ℚ) + (348959647 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7245099751 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12965]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12965 :
    2 * 160 < 12965 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999899 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12965 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12966 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12966. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12966 : WorldParameters where
  hiddenCharge := (1160830223 / 1000000000000 : ℝ)
  frame := (622021231789 / 1000000000000 : ℝ)
  moment := (8935154403 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12966 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (293160462073 / 200000000000 : ℝ)
    root := (2080262739 / 250000000000 : ℝ) }

noncomputable def scalar12966 : ScalarCertificate 12966 world12966 agent12966 where
  dimensionLo := 12966
  dimensionHi := 12966
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2275763399 / 1000000000000 : ℝ)
  frameLo := (622021231789 / 1000000000000 : ℝ)
  frameHi := (293160462073 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12966]
  agentFrame_pos := by norm_num only [agent12966]
  worldRadius := (2275763399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12966]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1162160057 / 1000000000000 : ℝ)
  lowerTail := (697387377 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7242144379 / 1000000000000 : ℝ)
  ledger := by
    have h : (1160830223 / 1000000000000 : ℚ) +
        (8935154403 / 1000000000000000000 : ℚ) / (2275763399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1162160057 / 1000000000000 : ℚ) + (697387377 / 500000000000 : ℚ) ≤
        (7242144379 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1160830223 / 1000000000000 : ℚ) +
        (8935154403 / 1000000000000000000 : ℚ) / (2275763399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1162160057 / 1000000000000 : ℚ) + (697387377 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7242144379 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12966]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12966 :
    2 * 160 < 12966 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999623 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12966 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12967 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12967. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12967 : WorldParameters where
  hiddenCharge := (290197389 / 250000000000 : ℝ)
  frame := (622007960863 / 1000000000000 : ℝ)
  moment := (2233338767 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12967 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (732886413613 / 500000000000 : ℝ)
    root := (8320420383 / 1000000000000 : ℝ) }

noncomputable def scalar12967 : ScalarCertificate 12967 world12967 agent12967 where
  dimensionLo := 12967
  dimensionHi := 12967
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2276125099 / 1000000000000 : ℝ)
  frameLo := (622007960863 / 1000000000000 : ℝ)
  frameHi := (732886413613 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12967]
  agentFrame_pos := by norm_num only [agent12967]
  worldRadius := (2276125099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12967]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1161206151 / 1000000000000 : ℝ)
  lowerTail := (1393711917 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1447838277 / 200000000000 : ℝ)
  ledger := by
    have h : (290197389 / 250000000000 : ℚ) +
        (2233338767 / 250000000000000000 : ℚ) / (2276125099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1161206151 / 1000000000000 : ℚ) + (1393711917 / 1000000000000 : ℚ) ≤
        (1447838277 / 200000000000 : ℚ) := by norm_num only
    have hc : (((290197389 / 250000000000 : ℚ) +
        (2233338767 / 250000000000000000 : ℚ) / (2276125099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1161206151 / 1000000000000 : ℚ) + (1393711917 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1447838277 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12967]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12967 :
    2 * 160 < 12967 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (399999883 / 40000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12967 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12968 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12968. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12968 : WorldParameters where
  hiddenCharge := (1160748899 / 1000000000000 : ℝ)
  frame := (155498673003 / 250000000000 : ℝ)
  moment := (111644453 / 12500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12968 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183217919533 / 125000000000 : ℝ)
    root := (831978999 / 100000000000 : ℝ) }

noncomputable def scalar12968 : ScalarCertificate 12968 world12968 agent12968 where
  dimensionLo := 12968
  dimensionHi := 12968
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2276486699 / 1000000000000 : ℝ)
  frameLo := (155498673003 / 250000000000 : ℝ)
  frameHi := (183217919533 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12968]
  agentFrame_pos := by norm_num only [agent12968]
  worldRadius := (2276486699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12968]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (580126533 / 500000000000 : ℝ)
  lowerTail := (87040621 / 62500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (723624081 / 100000000000 : ℝ)
  ledger := by
    have h : (1160748899 / 1000000000000 : ℚ) +
        (111644453 / 12500000000000000 : ℚ) / (2276486699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (580126533 / 500000000000 : ℚ) + (87040621 / 62500000000 : ℚ) ≤
        (723624081 / 100000000000 : ℚ) := by norm_num only
    have hc : (((1160748899 / 1000000000000 : ℚ) +
        (111644453 / 12500000000000000 : ℚ) / (2276486699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (580126533 / 500000000000 : ℚ) + (87040621 / 62500000000 : ℚ) : ℚ) : ℝ) ≤
        ((723624081 / 100000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12968]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12968 :
    2 * 160 < 12968 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996997 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12968 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12969 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12969. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12969 : WorldParameters where
  hiddenCharge := (1160708253 / 1000000000000 : ℝ)
  frame := (310990712619 / 500000000000 : ℝ)
  moment := (8929757917 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12969 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (357840307 / 244140625 : ℝ)
    root := (259973743 / 31250000000 : ℝ) }

noncomputable def scalar12969 : ScalarCertificate 12969 world12969 agent12969 where
  dimensionLo := 12969
  dimensionHi := 12969
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2276848399 / 1000000000000 : ℝ)
  frameLo := (310990712619 / 500000000000 : ℝ)
  frameHi := (357840307 / 244140625 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12969]
  agentFrame_pos := by norm_num only [agent12969]
  worldRadius := (2276848399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12969]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (72456309 / 62500000000 : ℝ)
  lowerTail := (139158897 / 100000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1808323163 / 250000000000 : ℝ)
  ledger := by
    have h : (1160708253 / 1000000000000 : ℚ) +
        (8929757917 / 1000000000000000000 : ℚ) / (2276848399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (72456309 / 62500000000 : ℚ) + (139158897 / 100000000000 : ℚ) ≤
        (1808323163 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1160708253 / 1000000000000 : ℚ) +
        (8929757917 / 1000000000000000000 : ℚ) / (2276848399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (72456309 / 62500000000 : ℚ) + (139158897 / 100000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1808323163 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12969]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12969 :
    2 * 160 < 12969 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999843 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12969 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12970 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12970. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12970 : WorldParameters where
  hiddenCharge := (580333809 / 500000000000 : ℝ)
  frame := (621968160539 / 1000000000000 : ℝ)
  moment := (89279601 / 10000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12970 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1465606144621 / 1000000000000 : ℝ)
    root := (8318529741 / 1000000000000 : ℝ) }

noncomputable def scalar12970 : ScalarCertificate 12970 world12970 agent12970 where
  dimensionLo := 12970
  dimensionHi := 12970
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2277325899 / 1000000000000 : ℝ)
  frameLo := (621968160539 / 1000000000000 : ℝ)
  frameHi := (1465606144621 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12970]
  agentFrame_pos := by norm_num only [agent12970]
  worldRadius := (2277325899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12970]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1158144537 / 1000000000000 : ℝ)
  lowerTail := (69513009 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7229697889 / 1000000000000 : ℝ)
  ledger := by
    have h : (580333809 / 500000000000 : ℚ) +
        (89279601 / 10000000000000000 : ℚ) / (2277325899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1158144537 / 1000000000000 : ℚ) + (69513009 / 50000000000 : ℚ) ≤
        (7229697889 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((580333809 / 500000000000 : ℚ) +
        (89279601 / 10000000000000000 : ℚ) / (2277325899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1158144537 / 1000000000000 : ℚ) + (69513009 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7229697889 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12970]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12970 :
    2 * 160 < 12970 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999701 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12970 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12971 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12971. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12971 : WorldParameters where
  hiddenCharge := (1160626993 / 1000000000000 : ℝ)
  frame := (310977448957 / 500000000000 : ℝ)
  moment := (8926162789 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12971 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (366394180689 / 250000000000 : ℝ)
    root := (1663579977 / 200000000000 : ℝ) }

noncomputable def scalar12971 : ScalarCertificate 12971 world12971 agent12971 where
  dimensionLo := 12971
  dimensionHi := 12971
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2277687599 / 1000000000000 : ℝ)
  frameLo := (310977448957 / 500000000000 : ℝ)
  frameHi := (366394180689 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12971]
  agentFrame_pos := by norm_num only [agent12971]
  worldRadius := (2277687599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12971]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (57859719 / 50000000000 : ℝ)
  lowerTail := (173650163 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7226755081 / 1000000000000 : ℝ)
  ledger := by
    have h : (1160626993 / 1000000000000 : ℚ) +
        (8926162789 / 1000000000000000000 : ℚ) / (2277687599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (57859719 / 50000000000 : ℚ) + (173650163 / 125000000000 : ℚ) ≤
        (7226755081 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1160626993 / 1000000000000 : ℚ) +
        (8926162789 / 1000000000000000000 : ℚ) / (2277687599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (57859719 / 50000000000 : ℚ) + (173650163 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7226755081 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12971]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12971 :
    2 * 160 < 12971 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (15999991 / 1600000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12971 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12972 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12972. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12972 : WorldParameters where
  hiddenCharge := (580293189 / 500000000000 : ℝ)
  frame := (621941637363 / 1000000000000 : ℝ)
  moment := (278886437 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12972 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1465547307177 / 1000000000000 : ℝ)
    root := (32489337 / 3906250000 : ℝ) }

noncomputable def scalar12972 : ScalarCertificate 12972 world12972 agent12972 where
  dimensionLo := 12972
  dimensionHi := 12972
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2278049399 / 1000000000000 : ℝ)
  frameLo := (621941637363 / 1000000000000 : ℝ)
  frameHi := (1465547307177 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12972]
  agentFrame_pos := by norm_num only [agent12972]
  worldRadius := (2278049399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12972]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (578122603 / 500000000000 : ℝ)
  lowerTail := (694071729 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3611907363 / 500000000000 : ℝ)
  ledger := by
    have h : (580293189 / 500000000000 : ℚ) +
        (278886437 / 31250000000000000 : ℚ) / (2278049399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (578122603 / 500000000000 : ℚ) + (694071729 / 500000000000 : ℚ) ≤
        (3611907363 / 500000000000 : ℚ) := by norm_num only
    have hc : (((580293189 / 500000000000 : ℚ) +
        (278886437 / 31250000000000000 : ℚ) / (2278049399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (578122603 / 500000000000 : ℚ) + (694071729 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3611907363 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12972]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12972 :
    2 * 160 < 12972 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999159 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12972 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12973 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12973. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12973 : WorldParameters where
  hiddenCharge := (46421831 / 40000000000 : ℝ)
  frame := (310964189443 / 500000000000 : ℝ)
  moment := (2230642421 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12973 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (366379477401 / 250000000000 : ℝ)
    root := (4158320387 / 500000000000 : ℝ) }

noncomputable def scalar12973 : ScalarCertificate 12973 world12973 agent12973 where
  dimensionLo := 12973
  dimensionHi := 12973
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2278410999 / 1000000000000 : ℝ)
  frameLo := (310964189443 / 500000000000 : ℝ)
  frameHi := (366379477401 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12973]
  agentFrame_pos := by norm_num only [agent12973]
  worldRadius := (2278410999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12973]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (577648377 / 500000000000 : ℝ)
  lowerTail := (277417273 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3610438367 / 500000000000 : ℝ)
  ledger := by
    have h : (46421831 / 40000000000 : ℚ) +
        (2230642421 / 250000000000000000 : ℚ) / (2278410999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (577648377 / 500000000000 : ℚ) + (277417273 / 200000000000 : ℚ) ≤
        (3610438367 / 500000000000 : ℚ) := by norm_num only
    have hc : (((46421831 / 40000000000 : ℚ) +
        (2230642421 / 250000000000000000 : ℚ) / (2278410999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (577648377 / 500000000000 : ℚ) + (277417273 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3610438367 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12973]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12973 :
    2 * 160 < 12973 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998961 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12973 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12974 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12974. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12974 : WorldParameters where
  hiddenCharge := (1160505181 / 1000000000000 : ℝ)
  frame := (310957561241 / 500000000000 : ℝ)
  moment := (8920773889 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12974 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (146548853003 / 100000000000 : ℝ)
    root := (4158005727 / 500000000000 : ℝ) }

noncomputable def scalar12974 : ScalarCertificate 12974 world12974 agent12974 where
  dimensionLo := 12974
  dimensionHi := 12974
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2278772699 / 1000000000000 : ℝ)
  frameLo := (310957561241 / 500000000000 : ℝ)
  frameHi := (146548853003 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12974]
  agentFrame_pos := by norm_num only [agent12974]
  worldRadius := (2278772699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12974]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (577174641 / 500000000000 : ℝ)
  lowerTail := (346507577 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1443588239 / 200000000000 : ℝ)
  ledger := by
    have h : (1160505181 / 1000000000000 : ℚ) +
        (8920773889 / 1000000000000000000 : ℚ) / (2278772699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (577174641 / 500000000000 : ℚ) + (346507577 / 250000000000 : ℚ) ≤
        (1443588239 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1160505181 / 1000000000000 : ℚ) +
        (8920773889 / 1000000000000000000 : ℚ) / (2278772699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (577174641 / 500000000000 : ℚ) + (346507577 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1443588239 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12974]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12974 :
    2 * 160 < 12974 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (249999907 / 25000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12974 {← IO.monoMsNow}" : IO Unit)
