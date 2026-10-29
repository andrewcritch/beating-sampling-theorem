import BstLean.Part243Row
#eval (do IO.println s!"p259-row-start 12975 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12975. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12975 : WorldParameters where
  hiddenCharge := (580232299 / 500000000000 : ℝ)
  frame := (621901868151 / 1000000000000 : ℝ)
  moment := (44594893 / 5000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12975 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1465459062919 / 1000000000000 : ℝ)
    root := (4157691157 / 500000000000 : ℝ) }

noncomputable def scalar12975 : ScalarCertificate 12975 world12975 agent12975 where
  dimensionLo := 12975
  dimensionHi := 12975
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2279134599 / 1000000000000 : ℝ)
  frameLo := (621901868151 / 1000000000000 : ℝ)
  frameHi := (1465459062919 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12975]
  agentFrame_pos := by norm_num only [agent12975]
  worldRadius := (2279134599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12975]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (576701237 / 500000000000 : ℝ)
  lowerTail := (1384974881 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3607503617 / 500000000000 : ℝ)
  ledger := by
    have h : (580232299 / 500000000000 : ℚ) +
        (44594893 / 5000000000000000 : ℚ) / (2279134599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (576701237 / 500000000000 : ℚ) + (1384974881 / 1000000000000 : ℚ) ≤
        (3607503617 / 500000000000 : ℚ) := by norm_num only
    have hc : (((580232299 / 500000000000 : ℚ) +
        (44594893 / 5000000000000000 : ℚ) / (2279134599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (576701237 / 500000000000 : ℚ) + (1384974881 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3607503617 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12975]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12975 :
    2 * 160 < 12975 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999847 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12975 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12976 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12976. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12976 : WorldParameters where
  hiddenCharge := (580212013 / 500000000000 : ℝ)
  frame := (621888615891 / 1000000000000 : ℝ)
  moment := (1783436763 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12976 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183178674611 / 125000000000 : ℝ)
    root := (1039344169 / 125000000000 : ℝ) }

noncomputable def scalar12976 : ScalarCertificate 12976 world12976 agent12976 where
  dimensionLo := 12976
  dimensionHi := 12976
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2279496799 / 1000000000000 : ℝ)
  frameLo := (621888615891 / 1000000000000 : ℝ)
  frameHi := (183178674611 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12976]
  agentFrame_pos := by norm_num only [agent12976]
  worldRadius := (2279496799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12976]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1152455991 / 1000000000000 : ℝ)
  lowerTail := (1383919651 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1803018483 / 250000000000 : ℝ)
  ledger := by
    have h : (580212013 / 500000000000 : ℚ) +
        (1783436763 / 200000000000000000 : ℚ) / (2279496799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1152455991 / 1000000000000 : ℚ) + (1383919651 / 1000000000000 : ℚ) ≤
        (1803018483 / 250000000000 : ℚ) := by norm_num only
    have hc : (((580212013 / 500000000000 : ℚ) +
        (1783436763 / 200000000000000000 : ℚ) / (2279496799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1152455991 / 1000000000000 : ℚ) + (1383919651 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1803018483 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12976]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12976 :
    2 * 160 < 12976 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999998291 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12976 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12977 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12977. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12977 : WorldParameters where
  hiddenCharge := (145047933 / 125000000000 : ℝ)
  frame := (621875365703 / 1000000000000 : ℝ)
  moment := (1783077907 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12977 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1465399742993 / 1000000000000 : ℝ)
    root := (1039265571 / 125000000000 : ℝ) }

noncomputable def scalar12977 : ScalarCertificate 12977 world12977 agent12977 where
  dimensionLo := 12977
  dimensionHi := 12977
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2279858999 / 1000000000000 : ℝ)
  frameLo := (621875365703 / 1000000000000 : ℝ)
  frameHi := (1465399742993 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12977]
  agentFrame_pos := by norm_num only [agent12977]
  worldRadius := (2279858999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12977]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (575755197 / 500000000000 : ℝ)
  lowerTail := (1382865349 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7209143031 / 1000000000000 : ℝ)
  ledger := by
    have h : (145047933 / 125000000000 : ℚ) +
        (1783077907 / 200000000000000000 : ℚ) / (2279858999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (575755197 / 500000000000 : ℚ) + (1382865349 / 1000000000000 : ℚ) ≤
        (7209143031 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((145047933 / 125000000000 : ℚ) +
        (1783077907 / 200000000000000000 : ℚ) / (2279858999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (575755197 / 500000000000 : ℚ) + (1382865349 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7209143031 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12977]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12977 :
    2 * 160 < 12977 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997119 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12977 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12978 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12978. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12978 : WorldParameters where
  hiddenCharge := (9065179 / 7812500000 : ℝ)
  frame := (310931058793 / 500000000000 : ℝ)
  moment := (8913595759 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12978 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (91585631693 / 62500000000 : ℝ)
    root := (4156747981 / 500000000000 : ℝ) }

noncomputable def scalar12978 : ScalarCertificate 12978 world12978 agent12978 where
  dimensionLo := 12978
  dimensionHi := 12978
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2280221199 / 1000000000000 : ℝ)
  frameLo := (310931058793 / 500000000000 : ℝ)
  frameHi := (91585631693 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12978]
  agentFrame_pos := by norm_num only [agent12978]
  worldRadius := (2280221199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12978]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (575282851 / 500000000000 : ℝ)
  lowerTail := (1381812001 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (450388411 / 62500000000 : ℝ)
  ledger := by
    have h : (9065179 / 7812500000 : ℚ) +
        (8913595759 / 1000000000000000000 : ℚ) / (2280221199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (575282851 / 500000000000 : ℚ) + (1381812001 / 1000000000000 : ℚ) ≤
        (450388411 / 62500000000 : ℚ) := by norm_num only
    have hc : (((9065179 / 7812500000 : ℚ) +
        (8913595759 / 1000000000000000000 : ℚ) / (2280221199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (575282851 / 500000000000 : ℚ) + (1381812001 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((450388411 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12978]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12978 :
    2 * 160 < 12978 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999521 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12978 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12979 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12979. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12979 : WorldParameters where
  hiddenCharge := (290075593 / 250000000000 : ℝ)
  frame := (31092443577 / 50000000000 : ℝ)
  moment := (1113975311 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12979 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1465340483303 / 1000000000000 : ℝ)
    root := (4156433799 / 500000000000 : ℝ) }

noncomputable def scalar12979 : ScalarCertificate 12979 world12979 agent12979 where
  dimensionLo := 12979
  dimensionHi := 12979
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2280583399 / 1000000000000 : ℝ)
  frameLo := (31092443577 / 50000000000 : ℝ)
  frameHi := (1465340483303 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12979]
  agentFrame_pos := by norm_num only [agent12979]
  worldRadius := (2280583399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12979]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1149621939 / 1000000000000 : ℝ)
  lowerTail := (11046077 / 8000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7203288607 / 1000000000000 : ℝ)
  ledger := by
    have h : (290075593 / 250000000000 : ℚ) +
        (1113975311 / 125000000000000000 : ℚ) / (2280583399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1149621939 / 1000000000000 : ℚ) + (11046077 / 8000000000 : ℚ) ≤
        (7203288607 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((290075593 / 250000000000 : ℚ) +
        (1113975311 / 125000000000000000 : ℚ) / (2280583399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1149621939 / 1000000000000 : ℚ) + (11046077 / 8000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7203288607 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12979]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12979 :
    2 * 160 < 12979 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (199999929 / 20000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12979 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12980 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12980. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12980 : WorldParameters where
  hiddenCharge := (1160261841 / 1000000000000 : ℝ)
  frame := (621835627563 / 1000000000000 : ℝ)
  moment := (222750243 / 25000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12980 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (146523267593 / 100000000000 : ℝ)
    root := (8312239349 / 1000000000000 : ℝ) }

noncomputable def scalar12980 : ScalarCertificate 12980 world12980 agent12980 where
  dimensionLo := 12980
  dimensionHi := 12980
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2281061599 / 1000000000000 : ℝ)
  frameLo := (621835627563 / 1000000000000 : ℝ)
  frameHi := (146523267593 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12980]
  agentFrame_pos := by norm_num only [agent12980]
  worldRadius := (2281061599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12980]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (287118941 / 250000000000 : ℝ)
  lowerTail := (344860429 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (449982569 / 62500000000 : ℝ)
  ledger := by
    have h : (1160261841 / 1000000000000 : ℚ) +
        (222750243 / 25000000000000000 : ℚ) / (2281061599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (287118941 / 250000000000 : ℚ) + (344860429 / 250000000000 : ℚ) ≤
        (449982569 / 62500000000 : ℚ) := by norm_num only
    have hc : (((1160261841 / 1000000000000 : ℚ) +
        (222750243 / 25000000000000000 : ℚ) / (2281061599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (287118941 / 250000000000 : ℚ) + (344860429 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((449982569 / 62500000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12980]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12980 :
    2 * 160 < 12980 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995199 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12980 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12981 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12981. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12981 : WorldParameters where
  hiddenCharge := (1160221321 / 1000000000000 : ℝ)
  frame := (77727798207 / 125000000000 : ℝ)
  moment := (8908217457 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12981 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1465203083119 / 1000000000000 : ℝ)
    root := (4155805639 / 500000000000 : ℝ) }

noncomputable def scalar12981 : ScalarCertificate 12981 world12981 agent12981 where
  dimensionLo := 12981
  dimensionHi := 12981
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2281423899 / 1000000000000 : ℝ)
  frameLo := (77727798207 / 125000000000 : ℝ)
  frameHi := (1465203083119 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12981]
  agentFrame_pos := by norm_num only [agent12981]
  worldRadius := (2281423899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12981]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (22950679 / 20000000000 : ℝ)
  lowerTail := (689195709 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7196800303 / 1000000000000 : ℝ)
  ledger := by
    have h : (1160221321 / 1000000000000 : ℚ) +
        (8908217457 / 1000000000000000000 : ℚ) / (2281423899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (22950679 / 20000000000 : ℚ) + (689195709 / 500000000000 : ℚ) ≤
        (7196800303 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1160221321 / 1000000000000 : ℚ) +
        (8908217457 / 1000000000000000000 : ℚ) / (2281423899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (22950679 / 20000000000 : ℚ) + (689195709 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7196800303 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12981]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12981 :
    2 * 160 < 12981 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999411 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12981 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12982 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12982. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12982 : WorldParameters where
  hiddenCharge := (290045203 / 250000000000 : ℝ)
  frame := (310904572909 / 500000000000 : ℝ)
  moment := (8906425697 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12982 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (146517350827 / 100000000000 : ℝ)
    root := (1038872923 / 125000000000 : ℝ) }

noncomputable def scalar12982 : ScalarCertificate 12982 world12982 agent12982 where
  dimensionLo := 12982
  dimensionHi := 12982
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2281786199 / 1000000000000 : ℝ)
  frameLo := (310904572909 / 500000000000 : ℝ)
  frameHi := (146517350827 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12982]
  agentFrame_pos := by norm_num only [agent12982]
  worldRadius := (2281786199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12982]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1146593039 / 1000000000000 : ℝ)
  lowerTail := (1377342071 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3596940969 / 500000000000 : ℝ)
  ledger := by
    have h : (290045203 / 250000000000 : ℚ) +
        (8906425697 / 1000000000000000000 : ℚ) / (2281786199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1146593039 / 1000000000000 : ℚ) + (1377342071 / 1000000000000 : ℚ) ≤
        (3596940969 / 500000000000 : ℚ) := by norm_num only
    have hc : (((290045203 / 250000000000 : ℚ) +
        (8906425697 / 1000000000000000000 : ℚ) / (2281786199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1146593039 / 1000000000000 : ℚ) + (1377342071 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3596940969 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12982]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12982 :
    2 * 160 < 12982 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (79999971 / 8000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12982 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12983 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12983. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12983 : WorldParameters where
  hiddenCharge := (1160140313 / 1000000000000 : ℝ)
  frame := (38862244253 / 62500000000 : ℝ)
  moment := (8904634441 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12983 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (732571972757 / 500000000000 : ℝ)
    root := (2077588917 / 250000000000 : ℝ) }

noncomputable def scalar12983 : ScalarCertificate 12983 world12983 agent12983 where
  dimensionLo := 12983
  dimensionHi := 12983
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2282148499 / 1000000000000 : ℝ)
  frameLo := (38862244253 / 62500000000 : ℝ)
  frameHi := (732571972757 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12983]
  agentFrame_pos := by norm_num only [agent12983]
  worldRadius := (2282148499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12983]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (572826503 / 500000000000 : ℝ)
  lowerTail := (275258729 / 200000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7190965959 / 1000000000000 : ℝ)
  ledger := by
    have h : (1160140313 / 1000000000000 : ℚ) +
        (8904634441 / 1000000000000000000 : ℚ) / (2282148499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (572826503 / 500000000000 : ℚ) + (275258729 / 200000000000 : ℚ) ≤
        (7190965959 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1160140313 / 1000000000000 : ℚ) +
        (8904634441 / 1000000000000000000 : ℚ) / (2282148499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (572826503 / 500000000000 : ℚ) + (275258729 / 200000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7190965959 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12983]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12983 :
    2 * 160 < 12983 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999998763 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12983 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12984 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12984. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12984 : WorldParameters where
  hiddenCharge := (72506239 / 62500000000 : ℝ)
  frame := (621782672347 / 1000000000000 : ℝ)
  moment := (8902843689 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12984 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (293022880141 / 200000000000 : ℝ)
    root := (830972813 / 100000000000 : ℝ) }

noncomputable def scalar12984 : ScalarCertificate 12984 world12984 agent12984 where
  dimensionLo := 12984
  dimensionHi := 12984
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2282510699 / 1000000000000 : ℝ)
  frameLo := (621782672347 / 1000000000000 : ℝ)
  frameHi := (293022880141 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12984]
  agentFrame_pos := by norm_num only [agent12984]
  worldRadius := (2282510699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12984]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (572356901 / 500000000000 : ℝ)
  lowerTail := (1375246089 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1797013103 / 250000000000 : ℝ)
  ledger := by
    have h : (72506239 / 62500000000 : ℚ) +
        (8902843689 / 1000000000000000000 : ℚ) / (2282510699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (572356901 / 500000000000 : ℚ) + (1375246089 / 1000000000000 : ℚ) ≤
        (1797013103 / 250000000000 : ℚ) := by norm_num only
    have hc : (((72506239 / 62500000000 : ℚ) +
        (8902843689 / 1000000000000000000 : ℚ) / (2282510699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (572356901 / 500000000000 : ℚ) + (1375246089 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1797013103 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12984]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12984 :
    2 * 160 < 12984 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (999999857 / 100000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12984 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12985 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12985. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12985 : WorldParameters where
  hiddenCharge := (580029673 / 500000000000 : ℝ)
  frame := (77721179839 / 125000000000 : ℝ)
  moment := (1738487 / 195312500000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12985 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1465084873837 / 1000000000000 : ℝ)
    root := (830910077 / 100000000000 : ℝ) }

noncomputable def scalar12985 : ScalarCertificate 12985 world12985 agent12985 where
  dimensionLo := 12985
  dimensionHi := 12985
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2282872999 / 1000000000000 : ℝ)
  frameLo := (77721179839 / 125000000000 : ℝ)
  frameHi := (1465084873837 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12985]
  agentFrame_pos := by norm_num only [agent12985]
  worldRadius := (2282872999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12985]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (71485973 / 62500000000 : ℝ)
  lowerTail := (1374199559 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1437028259 / 200000000000 : ℝ)
  ledger := by
    have h : (580029673 / 500000000000 : ℚ) +
        (1738487 / 195312500000000 : ℚ) / (2282872999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (71485973 / 62500000000 : ℚ) + (1374199559 / 1000000000000 : ℚ) ≤
        (1437028259 / 200000000000 : ℚ) := by norm_num only
    have hc : (((580029673 / 500000000000 : ℚ) +
        (1738487 / 195312500000000 : ℚ) / (2282872999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (71485973 / 62500000000 : ℚ) + (1374199559 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1437028259 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12985]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12985 :
    2 * 160 < 12985 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995773 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12985 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12986 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12986. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12986 : WorldParameters where
  hiddenCharge := (1160018879 / 1000000000000 : ℝ)
  frame := (124351241429 / 200000000000 : ℝ)
  moment := (8899263693 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12986 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1465055359041 / 1000000000000 : ℝ)
    root := (8308473587 / 1000000000000 : ℝ) }

noncomputable def scalar12986 : ScalarCertificate 12986 world12986 agent12986 where
  dimensionLo := 12986
  dimensionHi := 12986
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2283235299 / 1000000000000 : ℝ)
  frameLo := (124351241429 / 200000000000 : ℝ)
  frameHi := (1465055359041 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12986]
  agentFrame_pos := by norm_num only [agent12986]
  worldRadius := (2283235299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12986]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1142838211 / 1000000000000 : ℝ)
  lowerTail := (1373153949 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1795558139 / 250000000000 : ℝ)
  ledger := by
    have h : (1160018879 / 1000000000000 : ℚ) +
        (8899263693 / 1000000000000000000 : ℚ) / (2283235299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1142838211 / 1000000000000 : ℚ) + (1373153949 / 1000000000000 : ℚ) ≤
        (1795558139 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1160018879 / 1000000000000 : ℚ) +
        (8899263693 / 1000000000000000000 : ℚ) / (2283235299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1142838211 / 1000000000000 : ℚ) + (1373153949 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1795558139 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12986]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12986 :
    2 * 160 < 12986 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (499999799 / 50000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12986 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12987 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12987. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12987 : WorldParameters where
  hiddenCharge := (579989211 / 500000000000 : ℝ)
  frame := (155435744411 / 250000000000 : ℝ)
  moment := (177949489 / 20000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12987 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183128232039 / 125000000000 : ℝ)
    root := (8307846581 / 1000000000000 : ℝ) }

noncomputable def scalar12987 : ScalarCertificate 12987 world12987 agent12987 where
  dimensionLo := 12987
  dimensionHi := 12987
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2283597499 / 1000000000000 : ℝ)
  frameLo := (155435744411 / 250000000000 : ℝ)
  frameHi := (183128232039 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12987]
  agentFrame_pos := by norm_num only [agent12987]
  worldRadius := (2283597499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12987]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (570950829 / 500000000000 : ℝ)
  lowerTail := (686054589 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7179326193 / 1000000000000 : ℝ)
  ledger := by
    have h : (579989211 / 500000000000 : ℚ) +
        (177949489 / 20000000000000000 : ℚ) / (2283597499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (570950829 / 500000000000 : ℚ) + (686054589 / 500000000000 : ℚ) ≤
        (7179326193 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((579989211 / 500000000000 : ℚ) +
        (177949489 / 20000000000000000 : ℚ) / (2283597499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (570950829 / 500000000000 : ℚ) + (686054589 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7179326193 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12987]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12987 :
    2 * 160 < 12987 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999173 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12987 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12988 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12988. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12988 : WorldParameters where
  hiddenCharge := (46397519 / 40000000000 : ℝ)
  frame := (9714527347 / 15625000000 : ℝ)
  moment := (8895685709 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12988 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1464996371501 / 1000000000000 : ℝ)
    root := (1038402469 / 125000000000 : ℝ) }

noncomputable def scalar12988 : ScalarCertificate 12988 world12988 agent12988 where
  dimensionLo := 12988
  dimensionHi := 12988
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2283959899 / 1000000000000 : ℝ)
  frameLo := (9714527347 / 15625000000 : ℝ)
  frameHi := (1464996371501 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12988]
  agentFrame_pos := by norm_num only [agent12988]
  worldRadius := (2283959899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12988]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (570483071 / 500000000000 : ℝ)
  lowerTail := (1371065509 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1435284451 / 200000000000 : ℝ)
  ledger := by
    have h : (46397519 / 40000000000 : ℚ) +
        (8895685709 / 1000000000000000000 : ℚ) / (2283959899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (570483071 / 500000000000 : ℚ) + (1371065509 / 1000000000000 : ℚ) ≤
        (1435284451 / 200000000000 : ℚ) := by norm_num only
    have hc : (((46397519 / 40000000000 : ℚ) +
        (8895685709 / 1000000000000000000 : ℚ) / (2283959899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (570483071 / 500000000000 : ℚ) + (1371065509 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1435284451 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12988]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12988 :
    2 * 160 < 12988 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999999697 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12988 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12989 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12989. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12989 : WorldParameters where
  hiddenCharge := (1159897539 / 1000000000000 : ℝ)
  frame := (310858262419 / 500000000000 : ℝ)
  moment := (8893897471 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12989 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1464966904603 / 1000000000000 : ℝ)
    root := (8306593101 / 1000000000000 : ℝ) }

noncomputable def scalar12989 : ScalarCertificate 12989 world12989 agent12989 where
  dimensionLo := 12989
  dimensionHi := 12989
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2284322099 / 1000000000000 : ℝ)
  frameLo := (310858262419 / 500000000000 : ℝ)
  frameHi := (1464966904603 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12989]
  agentFrame_pos := by norm_num only [agent12989]
  worldRadius := (2284322099 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12989]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (57001569 / 50000000000 : ℝ)
  lowerTail := (685011313 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1434704147 / 200000000000 : ℝ)
  ledger := by
    have h : (1159897539 / 1000000000000 : ℚ) +
        (8893897471 / 1000000000000000000 : ℚ) / (2284322099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (57001569 / 50000000000 : ℚ) + (685011313 / 500000000000 : ℚ) ≤
        (1434704147 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1159897539 / 1000000000000 : ℚ) +
        (8893897471 / 1000000000000000000 : ℚ) / (2284322099 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (57001569 / 50000000000 : ℚ) + (685011313 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1434704147 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12989]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12989 :
    2 * 160 < 12989 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997529 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12989 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12990 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12990. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12990 : WorldParameters where
  hiddenCharge := (1159857113 / 1000000000000 : ℝ)
  frame := (621703301533 / 1000000000000 : ℝ)
  moment := (1778421947 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12990 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1464859358499 / 1000000000000 : ℝ)
    root := (4152983313 / 500000000000 : ℝ) }

noncomputable def scalar12990 : ScalarCertificate 12990 world12990 agent12990 where
  dimensionLo := 12990
  dimensionHi := 12990
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2284800599 / 1000000000000 : ℝ)
  frameLo := (621703301533 / 1000000000000 : ℝ)
  frameHi := (1464859358499 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12990]
  agentFrame_pos := by norm_num only [agent12990]
  worldRadius := (2284800599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12990]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (5694481 / 5000000000 : ℝ)
  lowerTail := (1368716621 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1792495709 / 250000000000 : ℝ)
  ledger := by
    have h : (1159857113 / 1000000000000 : ℚ) +
        (1778421947 / 200000000000000000 : ℚ) / (2284800599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (5694481 / 5000000000 : ℚ) + (1368716621 / 1000000000000 : ℚ) ≤
        (1792495709 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1159857113 / 1000000000000 : ℚ) +
        (1778421947 / 200000000000000000 : ℚ) / (2284800599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (5694481 / 5000000000 : ℚ) + (1368716621 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1792495709 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12990]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12990 :
    2 * 160 < 12990 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999657 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12990 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12991 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12991. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12991 : WorldParameters where
  hiddenCharge := (579908349 / 500000000000 : ℝ)
  frame := (155422520073 / 250000000000 : ℝ)
  moment := (8890322501 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12991 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (366207480607 / 250000000000 : ℝ)
    root := (8305340329 / 1000000000000 : ℝ) }

noncomputable def scalar12991 : ScalarCertificate 12991 world12991 agent12991 where
  dimensionLo := 12991
  dimensionHi := 12991
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2285162899 / 1000000000000 : ℝ)
  frameLo := (155422520073 / 250000000000 : ℝ)
  frameHi := (366207480607 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12991]
  agentFrame_pos := by norm_num only [agent12991]
  worldRadius := (2285162899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12991]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (284490853 / 250000000000 : ℝ)
  lowerTail := (4273987 / 3125000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7167086523 / 1000000000000 : ℝ)
  ledger := by
    have h : (579908349 / 500000000000 : ℚ) +
        (8890322501 / 1000000000000000000 : ℚ) / (2285162899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (284490853 / 250000000000 : ℚ) + (4273987 / 3125000000 : ℚ) ≤
        (7167086523 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((579908349 / 500000000000 : ℚ) +
        (8890322501 / 1000000000000000000 : ℚ) / (2285162899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (284490853 / 250000000000 : ℚ) + (4273987 / 3125000000 : ℚ) : ℚ) : ℝ) ≤
        ((7167086523 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12991]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12991 :
    2 * 160 < 12991 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (1999999261 / 200000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12991 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12992 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12992. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12992 : WorldParameters where
  hiddenCharge := (1159776293 / 1000000000000 : ℝ)
  frame := (124335372223 / 200000000000 : ℝ)
  moment := (8888535769 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12992 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1464800498389 / 1000000000000 : ℝ)
    root := (259522319 / 31250000000 : ℝ) }

noncomputable def scalar12992 : ScalarCertificate 12992 world12992 agent12992 where
  dimensionLo := 12992
  dimensionHi := 12992
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2285525299 / 1000000000000 : ℝ)
  frameLo := (124335372223 / 200000000000 : ℝ)
  frameHi := (1464800498389 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12992]
  agentFrame_pos := by norm_num only [agent12992]
  worldRadius := (2285525299 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12992]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (284257891 / 250000000000 : ℝ)
  lowerTail := (1366636051 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7164192573 / 1000000000000 : ℝ)
  ledger := by
    have h : (1159776293 / 1000000000000 : ℚ) +
        (8888535769 / 1000000000000000000 : ℚ) / (2285525299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (284257891 / 250000000000 : ℚ) + (1366636051 / 1000000000000 : ℚ) ≤
        (7164192573 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1159776293 / 1000000000000 : ℚ) +
        (8888535769 / 1000000000000000000 : ℚ) / (2285525299 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (284257891 / 250000000000 : ℚ) + (1366636051 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7164192573 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12992]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12992 :
    2 * 160 < 12992 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997209 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12992 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12993 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12993. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12993 : WorldParameters where
  hiddenCharge := (1159735899 / 1000000000000 : ℝ)
  frame := (621663644001 / 1000000000000 : ℝ)
  moment := (8886749539 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12993 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (732385546117 / 500000000000 : ℝ)
    root := (8304088263 / 1000000000000 : ℝ) }

noncomputable def scalar12993 : ScalarCertificate 12993 world12993 agent12993 where
  dimensionLo := 12993
  dimensionHi := 12993
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2285887599 / 1000000000000 : ℝ)
  frameLo := (621663644001 / 1000000000000 : ℝ)
  frameHi := (732385546117 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12993]
  agentFrame_pos := by norm_num only [agent12993]
  worldRadius := (2285887599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12993]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (142012567 / 125000000000 : ℝ)
  lowerTail := (1365597123 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7161301033 / 1000000000000 : ℝ)
  ledger := by
    have h : (1159735899 / 1000000000000 : ℚ) +
        (8886749539 / 1000000000000000000 : ℚ) / (2285887599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (142012567 / 125000000000 : ℚ) + (1365597123 / 1000000000000 : ℚ) ≤
        (7161301033 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1159735899 / 1000000000000 : ℚ) +
        (8886749539 / 1000000000000000000 : ℚ) / (2285887599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (142012567 / 125000000000 : ℚ) + (1365597123 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7161301033 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12993]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12993 :
    2 * 160 < 12993 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999995333 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12993 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12994 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12994. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12994 : WorldParameters where
  hiddenCharge := (231939103 / 200000000000 : ℝ)
  frame := (12433008579 / 20000000000 : ℝ)
  moment := (888496381 / 100000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12994 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (91546356131 / 62500000000 : ℝ)
    root := (259483203 / 31250000000 : ℝ) }

noncomputable def scalar12994 : ScalarCertificate 12994 world12994 agent12994 where
  dimensionLo := 12994
  dimensionHi := 12994
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2286249899 / 1000000000000 : ℝ)
  frameLo := (12433008579 / 20000000000 : ℝ)
  frameHi := (91546356131 / 62500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12994]
  agentFrame_pos := by norm_num only [agent12994]
  worldRadius := (2286249899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12994]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (567585189 / 500000000000 : ℝ)
  lowerTail := (682279553 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3579205927 / 500000000000 : ℝ)
  ledger := by
    have h : (231939103 / 200000000000 : ℚ) +
        (888496381 / 100000000000000000 : ℚ) / (2286249899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (567585189 / 500000000000 : ℚ) + (682279553 / 500000000000 : ℚ) ≤
        (3579205927 / 500000000000 : ℚ) := by norm_num only
    have hc : (((231939103 / 200000000000 : ℚ) +
        (888496381 / 100000000000000000 : ℚ) / (2286249899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (567585189 / 500000000000 : ℚ) + (682279553 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3579205927 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12994]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12994 :
    2 * 160 < 12994 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999996301 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12994 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12995 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12995. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12995 : WorldParameters where
  hiddenCharge := (1159655141 / 1000000000000 : ℝ)
  frame := (621637215961 / 1000000000000 : ℝ)
  moment := (8883178583 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12995 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1464712321829 / 1000000000000 : ℝ)
    root := (1660567381 / 200000000000 : ℝ) }

noncomputable def scalar12995 : ScalarCertificate 12995 world12995 agent12995 where
  dimensionLo := 12995
  dimensionHi := 12995
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2286612199 / 1000000000000 : ℝ)
  frameLo := (621637215961 / 1000000000000 : ℝ)
  frameHi := (1464712321829 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12995]
  agentFrame_pos := by norm_num only [agent12995]
  worldRadius := (2286612199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12995]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (283560277 / 250000000000 : ℝ)
  lowerTail := (1363522027 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (178888127 / 25000000000 : ℝ)
  ledger := by
    have h : (1159655141 / 1000000000000 : ℚ) +
        (8883178583 / 1000000000000000000 : ℚ) / (2286612199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (283560277 / 250000000000 : ℚ) + (1363522027 / 1000000000000 : ℚ) ≤
        (178888127 / 25000000000 : ℚ) := by norm_num only
    have hc : (((1159655141 / 1000000000000 : ℚ) +
        (8883178583 / 1000000000000000000 : ℚ) / (2286612199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (283560277 / 250000000000 : ℚ) + (1363522027 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((178888127 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12995]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12995 :
    2 * 160 < 12995 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999994447 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12995 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12996 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12996. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12996 : WorldParameters where
  hiddenCharge := (579807389 / 500000000000 : ℝ)
  frame := (310812002517 / 500000000000 : ℝ)
  moment := (8881393857 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12996 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (732341478783 / 500000000000 : ℝ)
    root := (8302211553 / 1000000000000 : ℝ) }

noncomputable def scalar12996 : ScalarCertificate 12996 world12996 agent12996 where
  dimensionLo := 12996
  dimensionHi := 12996
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2286974699 / 1000000000000 : ℝ)
  frameLo := (310812002517 / 500000000000 : ℝ)
  frameHi := (732341478783 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12996]
  agentFrame_pos := by norm_num only [agent12996]
  worldRadius := (2286974699 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12996]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1133312889 / 1000000000000 : ℝ)
  lowerTail := (68124303 / 50000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (28610563 / 4000000000 : ℝ)
  ledger := by
    have h : (579807389 / 500000000000 : ℚ) +
        (8881393857 / 1000000000000000000 : ℚ) / (2286974699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1133312889 / 1000000000000 : ℚ) + (68124303 / 50000000000 : ℚ) ≤
        (28610563 / 4000000000 : ℚ) := by norm_num only
    have hc : (((579807389 / 500000000000 : ℚ) +
        (8881393857 / 1000000000000000000 : ℚ) / (2286974699 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1133312889 / 1000000000000 : ℚ) + (68124303 / 50000000000 : ℚ) : ℚ) : ℝ) ≤
        ((28610563 / 4000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12996]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12996 :
    2 * 160 < 12996 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499998849 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12996 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12997 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12997. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12997 : WorldParameters where
  hiddenCharge := (579787213 / 500000000000 : ℝ)
  frame := (77701349521 / 125000000000 : ℝ)
  moment := (277487801 / 31250000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12997 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1464653605301 / 1000000000000 : ℝ)
    root := (8301586251 / 1000000000000 : ℝ) }

noncomputable def scalar12997 : ScalarCertificate 12997 world12997 agent12997 where
  dimensionLo := 12997
  dimensionHi := 12997
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2287336999 / 1000000000000 : ℝ)
  frameLo := (77701349521 / 125000000000 : ℝ)
  frameHi := (1464653605301 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12997]
  agentFrame_pos := by norm_num only [agent12997]
  worldRadius := (2287336999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12997]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (283096327 / 250000000000 : ℝ)
  lowerTail := (680725377 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1429951719 / 200000000000 : ℝ)
  ledger := by
    have h : (579787213 / 500000000000 : ℚ) +
        (277487801 / 31250000000000000 : ℚ) / (2287336999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (283096327 / 250000000000 : ℚ) + (680725377 / 500000000000 : ℚ) ≤
        (1429951719 / 200000000000 : ℚ) := by norm_num only
    have hc : (((579787213 / 500000000000 : ℚ) +
        (277487801 / 31250000000000000 : ℚ) / (2287336999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (283096327 / 250000000000 : ℚ) + (680725377 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1429951719 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12997]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12997 :
    2 * 160 < 12997 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (2499999783 / 250000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12997 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12998 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12998. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12998 : WorldParameters where
  hiddenCharge := (289883521 / 250000000000 : ℝ)
  frame := (621597589363 / 1000000000000 : ℝ)
  moment := (2219456477 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12998 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (732312135443 / 500000000000 : ℝ)
    root := (8300961189 / 1000000000000 : ℝ) }

noncomputable def scalar12998 : ScalarCertificate 12998 world12998 agent12998 where
  dimensionLo := 12998
  dimensionHi := 12998
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2287699399 / 1000000000000 : ℝ)
  frameLo := (621597589363 / 1000000000000 : ℝ)
  frameHi := (732312135443 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12998]
  agentFrame_pos := by norm_num only [agent12998]
  worldRadius := (2287699399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12998]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1131458727 / 1000000000000 : ℝ)
  lowerTail := (1360416507 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7146878927 / 1000000000000 : ℝ)
  ledger := by
    have h : (289883521 / 250000000000 : ℚ) +
        (2219456477 / 250000000000000000 : ℚ) / (2287699399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1131458727 / 1000000000000 : ℚ) + (1360416507 / 1000000000000 : ℚ) ≤
        (7146878927 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((289883521 / 250000000000 : ℚ) +
        (2219456477 / 250000000000000000 : ℚ) / (2287699399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1131458727 / 1000000000000 : ℚ) + (1360416507 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7146878927 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12998]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12998 :
    2 * 160 < 12998 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (4999999991 / 500000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12998 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 12999 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 12999. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part268
open Real BstLean.Part192 BstLean.Part243

noncomputable def world12999 : WorldParameters where
  hiddenCharge := (144936719 / 125000000000 : ℝ)
  frame := (310792192309 / 500000000000 : ℝ)
  moment := (1775208537 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent12999 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1464594954313 / 1000000000000 : ℝ)
    root := (4150168151 / 500000000000 : ℝ) }

noncomputable def scalar12999 : ScalarCertificate 12999 world12999 agent12999 where
  dimensionLo := 12999
  dimensionHi := 12999
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2288061799 / 1000000000000 : ℝ)
  frameLo := (310792192309 / 500000000000 : ℝ)
  frameHi := (1464594954313 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world12999]
  agentFrame_pos := by norm_num only [agent12999]
  worldRadius := (2288061799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent12999]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1130533031 / 1000000000000 : ℝ)
  lowerTail := (169922899 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1428800331 / 200000000000 : ℝ)
  ledger := by
    have h : (144936719 / 125000000000 : ℚ) +
        (1775208537 / 200000000000000000 : ℚ) / (2288061799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1130533031 / 1000000000000 : ℚ) + (169922899 / 125000000000 : ℚ) ≤
        (1428800331 / 200000000000 : ℚ) := by norm_num only
    have hc : (((144936719 / 125000000000 : ℚ) +
        (1775208537 / 200000000000000000 : ℚ) / (2288061799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1130533031 / 1000000000000 : ℚ) + (169922899 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1428800331 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world12999]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards12999 :
    2 * 160 < 12999 - 1 ∧
    (0 : ℝ) < (263 / 100000 : ℝ) ∧ (263 / 100000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (54839 / 250000 : ℝ) ∧
    (9999997923 / 1000000000000 : ℝ) ≤ (1 / 100 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part268

#eval (do IO.println s!"p259-row-end 12999 {← IO.monoMsNow}" : IO Unit)
