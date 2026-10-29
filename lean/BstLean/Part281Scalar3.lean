import BstLean.Part243Row
import BstLean.Part265Charge

#eval (do IO.println s!"p259-row-start 11934 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11934. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11934 : WorldParameters where
  hiddenCharge := (75571841 / 62500000000 : ℝ)
  frame := (318463986841 / 500000000000 : ℝ)
  moment := (5543759711 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11934 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736325561747 / 500000000000 : ℝ)
    root := (725173021 / 100000000000 : ℝ) }

noncomputable def scalar11934 : ScalarCertificate 11934 world11934 agent11934 where
  dimensionLo := 11934
  dimensionHi := 11934
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2403522599 / 1000000000000 : ℝ)
  frameLo := (318463986841 / 500000000000 : ℝ)
  frameHi := (736325561747 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11934]
  agentFrame_pos := by norm_num only [agent11934]
  worldRadius := (2403522599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11934]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (311405609 / 250000000000 : ℝ)
  lowerTail := (1594673617 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (60687499 / 7812500000 : ℝ)
  ledger := by
    have h : (75571841 / 62500000000 : ℚ) +
        (5543759711 / 500000000000000000 : ℚ) / (2403522599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (311405609 / 250000000000 : ℚ) + (1594673617 / 1000000000000 : ℚ) ≤
        (60687499 / 7812500000 : ℚ) := by norm_num only
    have hc : (((75571841 / 62500000000 : ℚ) +
        (5543759711 / 500000000000000000 : ℚ) / (2403522599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (311405609 / 250000000000 : ℚ) + (1594673617 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((60687499 / 7812500000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11934]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11934 :
    2 * 160 < 11934 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (439999967 / 40000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11934 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11935 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11935. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11935 : WorldParameters where
  hiddenCharge := (604547849 / 500000000000 : ℝ)
  frame := (636912247207 / 1000000000000 : ℝ)
  moment := (1385635647 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11935 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472605635099 / 1000000000000 : ℝ)
    root := (7251058503 / 1000000000000 : ℝ) }

noncomputable def scalar11935 : ScalarCertificate 11935 world11935 agent11935 where
  dimensionLo := 11935
  dimensionHi := 11935
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2403937199 / 1000000000000 : ℝ)
  frameLo := (636912247207 / 1000000000000 : ℝ)
  frameHi := (1472605635099 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11935]
  agentFrame_pos := by norm_num only [agent11935]
  worldRadius := (2403937199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11935]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (622250861 / 500000000000 : ℝ)
  lowerTail := (199168249 / 125000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (970551813 / 125000000000 : ℝ)
  ledger := by
    have h : (604547849 / 500000000000 : ℚ) +
        (1385635647 / 125000000000000000 : ℚ) / (2403937199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (622250861 / 500000000000 : ℚ) + (199168249 / 125000000000 : ℚ) ≤
        (970551813 / 125000000000 : ℚ) := by norm_num only
    have hc : (((604547849 / 500000000000 : ℚ) +
        (1385635647 / 125000000000000000 : ℚ) / (2403937199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (622250861 / 500000000000 : ℚ) + (199168249 / 125000000000 : ℚ) : ℚ) : ℝ) ≤
        ((970551813 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11935]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11935 :
    2 * 160 < 11935 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749998593 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11935 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11936 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11936. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11936 : WorldParameters where
  hiddenCharge := (241808391 / 200000000000 : ℝ)
  frame := (318448261727 / 500000000000 : ℝ)
  moment := (11082651677 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11936 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736280082533 / 500000000000 : ℝ)
    root := (7250387111 / 1000000000000 : ℝ) }

noncomputable def scalar11936 : ScalarCertificate 11936 world11936 agent11936 where
  dimensionLo := 11936
  dimensionHi := 11936
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2404351799 / 1000000000000 : ℝ)
  frameLo := (318448261727 / 500000000000 : ℝ)
  frameHi := (736280082533 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11936]
  agentFrame_pos := by norm_num only [agent11936]
  worldRadius := (2404351799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11936]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1243382229 / 1000000000000 : ℝ)
  lowerTail := (39800493 / 25000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7760832487 / 1000000000000 : ℝ)
  ledger := by
    have h : (241808391 / 200000000000 : ℚ) +
        (11082651677 / 1000000000000000000 : ℚ) / (2404351799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1243382229 / 1000000000000 : ℚ) + (39800493 / 25000000000 : ℚ) ≤
        (7760832487 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((241808391 / 200000000000 : ℚ) +
        (11082651677 / 1000000000000000000 : ℚ) / (2404351799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1243382229 / 1000000000000 : ℚ) + (39800493 / 25000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7760832487 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11936]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11936 :
    2 * 160 < 11936 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995143 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11936 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11937 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11937. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11937 : WorldParameters where
  hiddenCharge := (302247057 / 250000000000 : ℝ)
  frame := (318440401211 / 500000000000 : ℝ)
  moment := (443208757 / 40000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11937 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472514719341 / 1000000000000 : ℝ)
    root := (57997727 / 8000000000 : ℝ) }

noncomputable def scalar11937 : ScalarCertificate 11937 world11937 agent11937 where
  dimensionLo := 11937
  dimensionHi := 11937
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2404766499 / 1000000000000 : ℝ)
  frameLo := (318440401211 / 500000000000 : ℝ)
  frameHi := (1472514719341 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11937]
  agentFrame_pos := by norm_num only [agent11937]
  worldRadius := (2404766499 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11937]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1242263937 / 1000000000000 : ℝ)
  lowerTail := (1590694793 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3878626817 / 500000000000 : ℝ)
  ledger := by
    have h : (302247057 / 250000000000 : ℚ) +
        (443208757 / 40000000000000000 : ℚ) / (2404766499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1242263937 / 1000000000000 : ℚ) + (1590694793 / 1000000000000 : ℚ) ≤
        (3878626817 / 500000000000 : ℚ) := by norm_num only
    have hc : (((302247057 / 250000000000 : ℚ) +
        (443208757 / 40000000000000000 : ℚ) / (2404766499 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1242263937 / 1000000000000 : ℚ) + (1590694793 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3878626817 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11937]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11937 :
    2 * 160 < 11937 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749998899 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11937 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11938 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11938. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11938 : WorldParameters where
  hiddenCharge := (302233629 / 250000000000 : ℝ)
  frame := (63686508411 / 100000000000 : ℝ)
  moment := (5538893459 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11938 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472469297909 / 1000000000000 : ℝ)
    root := (57992359 / 8000000000 : ℝ) }

noncomputable def scalar11938 : ScalarCertificate 11938 world11938 agent11938 where
  dimensionLo := 11938
  dimensionHi := 11938
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2405180999 / 1000000000000 : ℝ)
  frameLo := (63686508411 / 100000000000 : ℝ)
  frameHi := (1472469297909 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11938]
  agentFrame_pos := by norm_num only [agent11938]
  worldRadius := (2405180999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11938]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (620573341 / 500000000000 : ℝ)
  lowerTail := (1589371013 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7753678059 / 1000000000000 : ℝ)
  ledger := by
    have h : (302233629 / 250000000000 : ℚ) +
        (5538893459 / 500000000000000000 : ℚ) / (2405180999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (620573341 / 500000000000 : ℚ) + (1589371013 / 1000000000000 : ℚ) ≤
        (7753678059 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((302233629 / 250000000000 : ℚ) +
        (5538893459 / 500000000000000000 : ℚ) / (2405180999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (620573341 / 500000000000 : ℚ) + (1589371013 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7753678059 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11938]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11938 :
    2 * 160 < 11938 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995701 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11938 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11939 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11939. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11939 : WorldParameters where
  hiddenCharge := (604440409 / 500000000000 : ℝ)
  frame := (318424684259 / 500000000000 : ℝ)
  moment := (11075355657 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11939 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472423900757 / 1000000000000 : ℝ)
    root := (724837411 / 100000000000 : ℝ) }

noncomputable def scalar11939 : ScalarCertificate 11939 world11939 agent11939 where
  dimensionLo := 11939
  dimensionHi := 11939
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2405595599 / 1000000000000 : ℝ)
  frameLo := (318424684259 / 500000000000 : ℝ)
  frameHi := (1472423900757 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11939]
  agentFrame_pos := by norm_num only [agent11939]
  worldRadius := (2405595599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11939]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1240030683 / 1000000000000 : ℝ)
  lowerTail := (397012159 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (48438161 / 6250000000 : ℝ)
  ledger := by
    have h : (604440409 / 500000000000 : ℚ) +
        (11075355657 / 1000000000000000000 : ℚ) / (2405595599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1240030683 / 1000000000000 : ℚ) + (397012159 / 250000000000 : ℚ) ≤
        (48438161 / 6250000000 : ℚ) := by norm_num only
    have hc : (((604440409 / 500000000000 : ℚ) +
        (11075355657 / 1000000000000000000 : ℚ) / (2405595599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1240030683 / 1000000000000 : ℚ) + (397012159 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((48438161 / 6250000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11939]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11939 :
    2 * 160 < 11939 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995427 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11939 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11940 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11940. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11940 : WorldParameters where
  hiddenCharge := (1208827137 / 1000000000000 : ℝ)
  frame := (159208413911 / 250000000000 : ℝ)
  moment := (11072925141 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11940 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147237852787 / 100000000000 : ℝ)
    root := (362385179 / 50000000000 : ℝ) }

noncomputable def scalar11940 : ScalarCertificate 11940 world11940 agent11940 where
  dimensionLo := 11940
  dimensionHi := 11940
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2406010199 / 1000000000000 : ℝ)
  frameLo := (159208413911 / 250000000000 : ℝ)
  frameHi := (147237852787 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11940]
  agentFrame_pos := by norm_num only [agent11940]
  worldRadius := (2406010199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11940]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (619457933 / 500000000000 : ℝ)
  lowerTail := (793363787 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7746536733 / 1000000000000 : ℝ)
  ledger := by
    have h : (1208827137 / 1000000000000 : ℚ) +
        (11072925141 / 1000000000000000000 : ℚ) / (2406010199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (619457933 / 500000000000 : ℚ) + (793363787 / 500000000000 : ℚ) ≤
        (7746536733 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1208827137 / 1000000000000 : ℚ) +
        (11072925141 / 1000000000000000000 : ℚ) / (2406010199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (619457933 / 500000000000 : ℚ) + (793363787 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7746536733 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11940]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11940 :
    2 * 160 < 11940 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999994743 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11940 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11941 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11941. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11941 : WorldParameters where
  hiddenCharge := (120877347 / 100000000000 : ℝ)
  frame := (636817945489 / 1000000000000 : ℝ)
  moment := (11070495371 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11941 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472333173277 / 1000000000000 : ℝ)
    root := (1449406657 / 200000000000 : ℝ) }

noncomputable def scalar11941 : ScalarCertificate 11941 world11941 agent11941 where
  dimensionLo := 11941
  dimensionHi := 11941
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2406424799 / 1000000000000 : ℝ)
  frameLo := (636817945489 / 1000000000000 : ℝ)
  frameHi := (1472333173277 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11941]
  agentFrame_pos := by norm_num only [agent11941]
  worldRadius := (2406424799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11941]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (309450551 / 250000000000 : ℝ)
  lowerTail := (1585407797 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (193574273 / 25000000000 : ℝ)
  ledger := by
    have h : (120877347 / 100000000000 : ℚ) +
        (11070495371 / 1000000000000000000 : ℚ) / (2406424799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (309450551 / 250000000000 : ℚ) + (1585407797 / 1000000000000 : ℚ) ≤
        (193574273 / 25000000000 : ℚ) := by norm_num only
    have hc : (((120877347 / 100000000000 : ℚ) +
        (11070495371 / 1000000000000000000 : ℚ) / (2406424799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (309450551 / 250000000000 : ℚ) + (1585407797 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((193574273 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11941]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11941 :
    2 * 160 < 11941 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999493 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11941 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11942 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11942. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11942 : WorldParameters where
  hiddenCharge := (604359909 / 500000000000 : ℝ)
  frame := (636802238051 / 1000000000000 : ℝ)
  moment := (2213613269 / 200000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11942 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (18403598111 / 12500000000 : ℝ)
    root := (289854529 / 40000000000 : ℝ) }

noncomputable def scalar11942 : ScalarCertificate 11942 world11942 agent11942 where
  dimensionLo := 11942
  dimensionHi := 11942
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2406839399 / 1000000000000 : ℝ)
  frameLo := (636802238051 / 1000000000000 : ℝ)
  frameHi := (18403598111 / 12500000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11942]
  agentFrame_pos := by norm_num only [agent11942]
  worldRadius := (2406839399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11942]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (77293109 / 62500000000 : ℝ)
  lowerTail := (1584089363 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (967426053 / 125000000000 : ℝ)
  ledger := by
    have h : (604359909 / 500000000000 : ℚ) +
        (2213613269 / 200000000000000000 : ℚ) / (2406839399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (77293109 / 62500000000 : ℚ) + (1584089363 / 1000000000000 : ℚ) ≤
        (967426053 / 125000000000 : ℚ) := by norm_num only
    have hc : (((604359909 / 500000000000 : ℚ) +
        (2213613269 / 200000000000000000 : ℚ) / (2406839399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (77293109 / 62500000000 : ℚ) + (1584089363 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((967426053 / 125000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11942]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11942 :
    2 * 160 < 11942 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998949 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11942 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11943 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11943. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11943 : WorldParameters where
  hiddenCharge := (604333091 / 500000000000 : ℝ)
  frame := (636786533329 / 1000000000000 : ℝ)
  moment := (691602379 / 62500000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11943 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736121274353 / 500000000000 : ℝ)
    root := (7245693399 / 1000000000000 : ℝ) }

noncomputable def scalar11943 : ScalarCertificate 11943 world11943 agent11943 where
  dimensionLo := 11943
  dimensionHi := 11943
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2407253999 / 1000000000000 : ℝ)
  frameLo := (636786533329 / 1000000000000 : ℝ)
  frameHi := (736121274353 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11943]
  agentFrame_pos := by norm_num only [agent11943]
  worldRadius := (2407253999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11943]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (61778923 / 50000000000 : ℝ)
  lowerTail := (1582772241 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7735849189 / 1000000000000 : ℝ)
  ledger := by
    have h : (604333091 / 500000000000 : ℚ) +
        (691602379 / 62500000000000000 : ℚ) / (2407253999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (61778923 / 50000000000 : ℚ) + (1582772241 / 1000000000000 : ℚ) ≤
        (7735849189 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((604333091 / 500000000000 : ℚ) +
        (691602379 / 62500000000000000 : ℚ) / (2407253999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (61778923 / 50000000000 : ℚ) + (1582772241 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7735849189 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11943]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11943 :
    2 * 160 < 11943 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997901 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11943 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11944 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11944. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11944 : WorldParameters where
  hiddenCharge := (15107657 / 12500000000 : ℝ)
  frame := (636770831323 / 1000000000000 : ℝ)
  moment := (11063210527 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11944 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (294439453357 / 200000000000 : ℝ)
    root := (113203497 / 15625000000 : ℝ) }

noncomputable def scalar11944 : ScalarCertificate 11944 world11944 agent11944 where
  dimensionLo := 11944
  dimensionHi := 11944
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2407668599 / 1000000000000 : ℝ)
  frameLo := (636770831323 / 1000000000000 : ℝ)
  frameHi := (294439453357 / 200000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11944]
  agentFrame_pos := by norm_num only [agent11944]
  worldRadius := (2407668599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11944]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1234468329 / 1000000000000 : ℝ)
  lowerTail := (1581456397 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3866146579 / 500000000000 : ℝ)
  ledger := by
    have h : (15107657 / 12500000000 : ℚ) +
        (11063210527 / 1000000000000000000 : ℚ) / (2407668599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1234468329 / 1000000000000 : ℚ) + (1581456397 / 1000000000000 : ℚ) ≤
        (3866146579 / 500000000000 : ℚ) := by norm_num only
    have hc : (((15107657 / 12500000000 : ℚ) +
        (11063210527 / 1000000000000000000 : ℚ) / (2407668599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1234468329 / 1000000000000 : ℚ) + (1581456397 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3866146579 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11944]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11944 :
    2 * 160 < 11944 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499999527 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11944 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11945 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11945. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11945 : WorldParameters where
  hiddenCharge := (604279477 / 500000000000 : ℝ)
  frame := (4974649469 / 7812500000 : ℝ)
  moment := (11060783733 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11945 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472152015017 / 1000000000000 : ℝ)
    root := (7244354451 / 1000000000000 : ℝ) }

noncomputable def scalar11945 : ScalarCertificate 11945 world11945 agent11945 where
  dimensionLo := 11945
  dimensionHi := 11945
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2408083199 / 1000000000000 : ℝ)
  frameLo := (4974649469 / 7812500000 : ℝ)
  frameHi := (1472152015017 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11945]
  agentFrame_pos := by norm_num only [agent11945]
  worldRadius := (2408083199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11945]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (616679697 / 500000000000 : ℝ)
  lowerTail := (1580141893 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3864370217 / 500000000000 : ℝ)
  ledger := by
    have h : (604279477 / 500000000000 : ℚ) +
        (11060783733 / 1000000000000000000 : ℚ) / (2408083199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (616679697 / 500000000000 : ℚ) + (1580141893 / 1000000000000 : ℚ) ≤
        (3864370217 / 500000000000 : ℚ) := by norm_num only
    have hc : (((604279477 / 500000000000 : ℚ) +
        (11060783733 / 1000000000000000000 : ℚ) / (2408083199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (616679697 / 500000000000 : ℚ) + (1580141893 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3864370217 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11945]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11945 :
    2 * 160 < 11945 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199999173 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11945 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11946 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11946. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11946 : WorldParameters where
  hiddenCharge := (1208505363 / 1000000000000 : ℝ)
  frame := (9949053679 / 15625000000 : ℝ)
  moment := (2764589421 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11946 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (58884271259 / 40000000000 : ℝ)
    root := (7243685329 / 1000000000000 : ℝ) }

noncomputable def scalar11946 : ScalarCertificate 11946 world11946 agent11946 where
  dimensionLo := 11946
  dimensionHi := 11946
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2408497899 / 1000000000000 : ℝ)
  frameLo := (9949053679 / 15625000000 : ℝ)
  frameHi := (58884271259 / 40000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11946]
  agentFrame_pos := by norm_num only [agent11946]
  worldRadius := (2408497899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11946]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (616125841 / 500000000000 : ℝ)
  lowerTail := (1263063 / 800000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7725190907 / 1000000000000 : ℝ)
  ledger := by
    have h : (1208505363 / 1000000000000 : ℚ) +
        (2764589421 / 250000000000000000 : ℚ) / (2408497899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (616125841 / 500000000000 : ℚ) + (1263063 / 800000000 : ℚ) ≤
        (7725190907 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1208505363 / 1000000000000 : ℚ) +
        (2764589421 / 250000000000000000 : ℚ) / (2408497899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (616125841 / 500000000000 : ℚ) + (1263063 / 800000000 : ℚ) : ℚ) : ℝ) ≤
        ((7725190907 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11946]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11946 :
    2 * 160 < 11946 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997967 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11946 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11947 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11947. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11947 : WorldParameters where
  hiddenCharge := (1208451787 / 1000000000000 : ℝ)
  frame := (636723741593 / 1000000000000 : ℝ)
  moment := (11055932377 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11947 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (736030786051 / 500000000000 : ℝ)
    root := (7243016519 / 1000000000000 : ℝ) }

noncomputable def scalar11947 : ScalarCertificate 11947 world11947 agent11947 where
  dimensionLo := 11947
  dimensionHi := 11947
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2408912399 / 1000000000000 : ℝ)
  frameLo := (636723741593 / 1000000000000 : ℝ)
  frameHi := (736030786051 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11947]
  agentFrame_pos := by norm_num only [agent11947]
  worldRadius := (2408912399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11947]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (307786263 / 250000000000 : ℝ)
  lowerTail := (1577516803 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1544328949 / 200000000000 : ℝ)
  ledger := by
    have h : (1208451787 / 1000000000000 : ℚ) +
        (11055932377 / 1000000000000000000 : ℚ) / (2408912399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (307786263 / 250000000000 : ℚ) + (1577516803 / 1000000000000 : ℚ) ≤
        (1544328949 / 200000000000 : ℚ) := by norm_num only
    have hc : (((1208451787 / 1000000000000 : ℚ) +
        (11055932377 / 1000000000000000000 : ℚ) / (2408912399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (307786263 / 250000000000 : ℚ) + (1577516803 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1544328949 / 200000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11947]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11947 :
    2 * 160 < 11947 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (219999989 / 20000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11947 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11948 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11948. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11948 : WorldParameters where
  hiddenCharge := (604199113 / 500000000000 : ℝ)
  frame := (636708050443 / 1000000000000 : ℝ)
  moment := (5526753907 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11948 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1472016392839 / 1000000000000 : ℝ)
    root := (1448469573 / 200000000000 : ℝ) }

noncomputable def scalar11948 : ScalarCertificate 11948 world11948 agent11948 where
  dimensionLo := 11948
  dimensionHi := 11948
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2409326999 / 1000000000000 : ℝ)
  frameLo := (636708050443 / 1000000000000 : ℝ)
  frameHi := (1472016392839 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11948]
  agentFrame_pos := by norm_num only [agent11948]
  worldRadius := (2409326999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11948]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (123003963 / 100000000000 : ℝ)
  lowerTail := (788103107 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7718101759 / 1000000000000 : ℝ)
  ledger := by
    have h : (604199113 / 500000000000 : ℚ) +
        (5526753907 / 500000000000000000 : ℚ) / (2409326999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (123003963 / 100000000000 : ℚ) + (788103107 / 500000000000 : ℚ) ≤
        (7718101759 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((604199113 / 500000000000 : ℚ) +
        (5526753907 / 500000000000000000 : ℚ) / (2409326999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (123003963 / 100000000000 : ℚ) + (788103107 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7718101759 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11948]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11948 :
    2 * 160 < 11948 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499997197 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11948 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11949 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11949. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11949 : WorldParameters where
  hiddenCharge := (30208617 / 25000000000 : ℝ)
  frame := (127338472401 / 200000000000 : ℝ)
  moment := (5525541997 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11949 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471971231761 / 1000000000000 : ℝ)
    root := (7241679443 / 1000000000000 : ℝ) }

noncomputable def scalar11949 : ScalarCertificate 11949 world11949 agent11949 where
  dimensionLo := 11949
  dimensionHi := 11949
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2409741599 / 1000000000000 : ℝ)
  frameLo := (127338472401 / 200000000000 : ℝ)
  frameHi := (1471971231761 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11949]
  agentFrame_pos := by norm_num only [agent11949]
  worldRadius := (2409741599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11949]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1228935353 / 1000000000000 : ℝ)
  lowerTail := (1574896897 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (192864049 / 25000000000 : ℝ)
  ledger := by
    have h : (30208617 / 25000000000 : ℚ) +
        (5525541997 / 500000000000000000 : ℚ) / (2409741599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1228935353 / 1000000000000 : ℚ) + (1574896897 / 1000000000000 : ℚ) ≤
        (192864049 / 25000000000 : ℚ) := by norm_num only
    have hc : (((30208617 / 25000000000 : ℚ) +
        (5525541997 / 500000000000000000 : ℚ) / (2409741599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1228935353 / 1000000000000 : ℚ) + (1574896897 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((192864049 / 25000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11949]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11949 :
    2 * 160 < 11949 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2199998909 / 200000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11949 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11950 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11950. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11950 : WorldParameters where
  hiddenCharge := (24165823 / 20000000000 : ℝ)
  frame := (318338338139 / 500000000000 : ℝ)
  moment := (2762165229 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11950 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (183990761107 / 125000000000 : ℝ)
    root := (905126407 / 125000000000 : ℝ) }

noncomputable def scalar11950 : ScalarCertificate 11950 world11950 agent11950 where
  dimensionLo := 11950
  dimensionHi := 11950
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2410156199 / 1000000000000 : ℝ)
  frameLo := (318338338139 / 500000000000 : ℝ)
  frameHi := (183990761107 / 125000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11950]
  agentFrame_pos := by norm_num only [agent11950]
  worldRadius := (2410156199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11950]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (61391611 / 50000000000 : ℝ)
  lowerTail := (31471777 / 20000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7711025343 / 1000000000000 : ℝ)
  ledger := by
    have h : (24165823 / 20000000000 : ℚ) +
        (2762165229 / 250000000000000000 : ℚ) / (2410156199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (61391611 / 50000000000 : ℚ) + (31471777 / 20000000000 : ℚ) ≤
        (7711025343 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((24165823 / 20000000000 : ℚ) +
        (2762165229 / 250000000000000000 : ℚ) / (2410156199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (61391611 / 50000000000 : ℚ) + (31471777 / 20000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7711025343 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11950]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11950 :
    2 * 160 < 11950 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (274999997 / 25000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11950 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11951 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11951. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11951 : WorldParameters where
  hiddenCharge := (604118817 / 500000000000 : ℝ)
  frame := (318330496631 / 500000000000 : ℝ)
  moment := (552311929 / 50000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11951 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (73594048801 / 50000000000 : ℝ)
    root := (7240343301 / 1000000000000 : ℝ) }

noncomputable def scalar11951 : ScalarCertificate 11951 world11951 agent11951 where
  dimensionLo := 11951
  dimensionHi := 11951
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2410570899 / 1000000000000 : ℝ)
  frameLo := (318330496631 / 500000000000 : ℝ)
  frameHi := (73594048801 / 50000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11951]
  agentFrame_pos := by norm_num only [agent11951]
  worldRadius := (2410570899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11951]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1226730347 / 1000000000000 : ℝ)
  lowerTail := (1572282219 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7707492011 / 1000000000000 : ℝ)
  ledger := by
    have h : (604118817 / 500000000000 : ℚ) +
        (552311929 / 50000000000000000 : ℚ) / (2410570899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1226730347 / 1000000000000 : ℚ) + (1572282219 / 1000000000000 : ℚ) ≤
        (7707492011 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((604118817 / 500000000000 : ℚ) +
        (552311929 / 50000000000000000 : ℚ) / (2410570899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1226730347 / 1000000000000 : ℚ) + (1572282219 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7707492011 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11951]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11951 :
    2 * 160 < 11951 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (1374999823 / 125000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11951 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11952 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11952. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11952 : WorldParameters where
  hiddenCharge := (1208184133 / 1000000000000 : ℝ)
  frame := (127329062591 / 200000000000 : ℝ)
  moment := (5521908493 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11952 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (367958971821 / 250000000000 : ℝ)
    root := (361983779 / 50000000000 : ℝ) }

noncomputable def scalar11952 : ScalarCertificate 11952 world11952 agent11952 where
  dimensionLo := 11952
  dimensionHi := 11952
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2410985399 / 1000000000000 : ℝ)
  frameLo := (127329062591 / 200000000000 : ℝ)
  frameHi := (367958971821 / 250000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11952]
  agentFrame_pos := by norm_num only [agent11952]
  worldRadius := (2410985399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11952]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (612814747 / 500000000000 : ℝ)
  lowerTail := (785488357 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (1925990477 / 250000000000 : ℝ)
  ledger := by
    have h : (1208184133 / 1000000000000 : ℚ) +
        (5521908493 / 500000000000000000 : ℚ) / (2410985399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (612814747 / 500000000000 : ℚ) + (785488357 / 500000000000 : ℚ) ≤
        (1925990477 / 250000000000 : ℚ) := by norm_num only
    have hc : (((1208184133 / 1000000000000 : ℚ) +
        (5521908493 / 500000000000000000 : ℚ) / (2410985399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (612814747 / 500000000000 : ℚ) + (785488357 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((1925990477 / 250000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11952]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11952 :
    2 * 160 < 11952 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (5499998259 / 500000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11952 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11953 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11953. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11953 : WorldParameters where
  hiddenCharge := (151016331 / 125000000000 : ℝ)
  frame := (318314817679 / 500000000000 : ℝ)
  moment := (11041396133 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11953 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (36794770417 / 25000000000 : ℝ)
    root := (1809752023 / 250000000000 : ℝ) }

noncomputable def scalar11953 : ScalarCertificate 11953 world11953 agent11953 where
  dimensionLo := 11953
  dimensionHi := 11953
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2411399999 / 1000000000000 : ℝ)
  frameLo := (318314817679 / 500000000000 : ℝ)
  frameHi := (36794770417 / 25000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11953]
  agentFrame_pos := by norm_num only [agent11953]
  worldRadius := (2411399999 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11953]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (306132463 / 250000000000 : ℝ)
  lowerTail := (19620907 / 12500000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7700434977 / 1000000000000 : ℝ)
  ledger := by
    have h : (151016331 / 125000000000 : ℚ) +
        (11041396133 / 1000000000000000000 : ℚ) / (2411399999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (306132463 / 250000000000 : ℚ) + (19620907 / 12500000000 : ℚ) ≤
        (7700434977 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((151016331 / 125000000000 : ℚ) +
        (11041396133 / 1000000000000000000 : ℚ) / (2411399999 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (306132463 / 250000000000 : ℚ) + (19620907 / 12500000000 : ℚ) : ℚ) : ℝ) ≤
        ((7700434977 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11953]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11953 :
    2 * 160 < 11953 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999999553 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11953 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11954 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11954. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11954 : WorldParameters where
  hiddenCharge := (604038589 / 500000000000 : ℝ)
  frame := (636613960469 / 1000000000000 : ℝ)
  moment := (5519488011 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11954 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735872888051 / 500000000000 : ℝ)
    root := (7238340837 / 1000000000000 : ℝ) }

noncomputable def scalar11954 : ScalarCertificate 11954 world11954 agent11954 where
  dimensionLo := 11954
  dimensionHi := 11954
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2411814599 / 1000000000000 : ℝ)
  frameLo := (636613960469 / 1000000000000 : ℝ)
  frameHi := (735872888051 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11954]
  agentFrame_pos := by norm_num only [agent11954]
  worldRadius := (2411814599 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11954]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (244686279 / 200000000000 : ℝ)
  lowerTail := (392092433 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7696911319 / 1000000000000 : ℝ)
  ledger := by
    have h : (604038589 / 500000000000 : ℚ) +
        (5519488011 / 500000000000000000 : ℚ) / (2411814599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (244686279 / 200000000000 : ℚ) + (392092433 / 250000000000 : ℚ) ≤
        (7696911319 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((604038589 / 500000000000 : ℚ) +
        (5519488011 / 500000000000000000 : ℚ) / (2411814599 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (244686279 / 200000000000 : ℚ) + (392092433 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7696911319 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11954]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11954 :
    2 * 160 < 11954 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (549999793 / 50000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11954 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11955 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11955. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11955 : WorldParameters where
  hiddenCharge := (604011861 / 500000000000 : ℝ)
  frame := (636598288287 / 1000000000000 : ℝ)
  moment := (2759139163 / 250000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11955 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471700753629 / 1000000000000 : ℝ)
    root := (1447534763 / 200000000000 : ℝ) }

noncomputable def scalar11955 : ScalarCertificate 11955 world11955 agent11955 where
  dimensionLo := 11955
  dimensionHi := 11955
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2412229199 / 1000000000000 : ℝ)
  frameLo := (636598288287 / 1000000000000 : ℝ)
  frameHi := (1471700753629 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11955]
  agentFrame_pos := by norm_num only [agent11955]
  worldRadius := (2412229199 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11955]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (611167037 / 500000000000 : ℝ)
  lowerTail := (783534083 / 500000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7693390827 / 1000000000000 : ℝ)
  ledger := by
    have h : (604011861 / 500000000000 : ℚ) +
        (2759139163 / 250000000000000000 : ℚ) / (2412229199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (611167037 / 500000000000 : ℚ) + (783534083 / 500000000000 : ℚ) ≤
        (7693390827 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((604011861 / 500000000000 : ℚ) +
        (2759139163 / 250000000000000000 : ℚ) / (2412229199 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (611167037 / 500000000000 : ℚ) + (783534083 / 500000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7693390827 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11955]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11955 :
    2 * 160 < 11955 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (2749999303 / 250000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11955 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11956 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11956. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11956 : WorldParameters where
  hiddenCharge := (603985141 / 500000000000 : ℝ)
  frame := (636582618813 / 1000000000000 : ℝ)
  moment := (5517069011 / 500000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11956 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (735827877601 / 500000000000 : ℝ)
    root := (289480281 / 40000000000 : ℝ) }

noncomputable def scalar11956 : ScalarCertificate 11956 world11956 agent11956 where
  dimensionLo := 11956
  dimensionHi := 11956
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2412643799 / 1000000000000 : ℝ)
  frameLo := (636582618813 / 1000000000000 : ℝ)
  frameHi := (735827877601 / 500000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11956]
  agentFrame_pos := by norm_num only [agent11956]
  worldRadius := (2412643799 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11956]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (1221237911 / 1000000000000 : ℝ)
  lowerTail := (391441973 / 250000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (153797471 / 20000000000 : ℝ)
  ledger := by
    have h : (603985141 / 500000000000 : ℚ) +
        (5517069011 / 500000000000000000 : ℚ) / (2412643799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1221237911 / 1000000000000 : ℚ) + (391441973 / 250000000000 : ℚ) ≤
        (153797471 / 20000000000 : ℚ) := by norm_num only
    have hc : (((603985141 / 500000000000 : ℚ) +
        (5517069011 / 500000000000000000 : ℚ) / (2412643799 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (1221237911 / 1000000000000 : ℚ) + (391441973 / 250000000000 : ℚ) : ℚ) : ℝ) ≤
        ((153797471 / 20000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11956]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11956 :
    2 * 160 < 11956 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (137499971 / 12500000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11956 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11957 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11957. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11957 : WorldParameters where
  hiddenCharge := (1207916857 / 1000000000000 : ℝ)
  frame := (159141738011 / 250000000000 : ℝ)
  moment := (11031720133 / 1000000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11957 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (1471610780807 / 1000000000000 : ℝ)
    root := (7236340467 / 1000000000000 : ℝ) }

noncomputable def scalar11957 : ScalarCertificate 11957 world11957 agent11957 where
  dimensionLo := 11957
  dimensionHi := 11957
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2413058399 / 1000000000000 : ℝ)
  frameLo := (159141738011 / 250000000000 : ℝ)
  frameHi := (1471610780807 / 1000000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11957]
  agentFrame_pos := by norm_num only [agent11957]
  worldRadius := (2413058399 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11957]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (152517863 / 125000000000 : ℝ)
  lowerTail := (1564468909 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (7686359483 / 1000000000000 : ℝ)
  ledger := by
    have h : (1207916857 / 1000000000000 : ℚ) +
        (11031720133 / 1000000000000000000 : ℚ) / (2413058399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (152517863 / 125000000000 : ℚ) + (1564468909 / 1000000000000 : ℚ) ≤
        (7686359483 / 1000000000000 : ℚ) := by norm_num only
    have hc : (((1207916857 / 1000000000000 : ℚ) +
        (11031720133 / 1000000000000000000 : ℚ) / (2413058399 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (152517863 / 125000000000 : ℚ) + (1564468909 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((7686359483 / 1000000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11957]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11957 :
    2 * 160 < 11957 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999997233 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11957 {← IO.monoMsNow}" : IO Unit)

#eval (do IO.println s!"p259-row-start 11958 {← IO.monoMsNow}" : IO Unit)

/-! Stored rational proposals at dimension 11958. These declarations check the
scalar ledger only. They do not supply the endpoint tails or network packages. -/
namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

noncomputable def world11958 : WorldParameters where
  hiddenCharge := (1207863447 / 1000000000000 : ℝ)
  frame := (636551287981 / 1000000000000 : ℝ)
  moment := (1378662873 / 125000000000000000 : ℝ)
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 54 / 100

noncomputable def agent11958 : AgentParameters :=
  { agentLedgerParameters with
    charge := (359829 / 200000000 : ℝ)
    frame := (147156583043 / 100000000000 : ℝ)
    root := (3617837071 / 500000000000 : ℝ) }

noncomputable def scalar11958 : ScalarCertificate 11958 world11958 agent11958 where
  dimensionLo := 11958
  dimensionHi := 11958
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 54 / 100
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := (2413472899 / 1000000000000 : ℝ)
  frameLo := (636551287981 / 1000000000000 : ℝ)
  frameHi := (147156583043 / 100000000000 : ℝ)
  noise_order := by norm_num only <;> simp only [true_and]
  overlap_order := by norm_num only <;> simp only [true_and]
  radius_order := by norm_num only <;> simp only [true_and]
  frame_order := by norm_num only <;> simp only [true_and]
  worldFrame_pos := by norm_num only [world11958]
  agentFrame_pos := by norm_num only [agent11958]
  worldRadius := (2413472899 / 1000000000000 : ℝ)
  worldRadius_pos := by norm_num only <;> simp only [true_and]
  agentRoot_nonneg := by norm_num only [agent11958]
  retainedCharge := (359829 / 200000000 : ℝ)
  samplingCharge := 1 / 10 ^ 12
  upperTail := (609524491 / 500000000000 : ℝ)
  lowerTail := (1563171129 / 1000000000000 : ℝ)
  retainedCharge_nonneg := by norm_num only <;> simp only [true_and]
  samplingCharge_nonneg := by norm_num only <;> simp only [true_and]
  upperTail_nonneg := by norm_num only <;> simp only [true_and]
  lowerTail_nonneg := by norm_num only <;> simp only [true_and]
  totalBudget := (3841424311 / 500000000000 : ℝ)
  ledger := by
    have h : (1207863447 / 1000000000000 : ℚ) +
        (1378662873 / 125000000000000000 : ℚ) / (2413472899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (609524491 / 500000000000 : ℚ) + (1563171129 / 1000000000000 : ℚ) ≤
        (3841424311 / 500000000000 : ℚ) := by norm_num only
    have hc : (((1207863447 / 1000000000000 : ℚ) +
        (1378662873 / 125000000000000000 : ℚ) / (2413472899 / 1000000000000 : ℚ) ^ 2 +
        (359829 / 200000000 : ℚ) + (1 / 10 ^ 12 : ℚ) +
        (609524491 / 500000000000 : ℚ) + (1563171129 / 1000000000000 : ℚ) : ℚ) : ℝ) ≤
        ((3841424311 / 500000000000 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    dsimp only [world11958]
    exact hc
  budget := by norm_num only <;> simp only [true_and]

theorem guards11958 :
    2 * 160 < 11958 - 1 ∧
    (0 : ℝ) < (2147 / 1000000 : ℝ) ∧ (2147 / 1000000 : ℝ) < 1 / 2 ∧
    (1 / 5 : ℝ) < (5381 / 25000 : ℝ) ∧
    (10999995843 / 1000000000000 : ℝ) ≤ (11 / 1000 : ℝ) := by norm_num only <;> simp only [true_and]

end BstLean.Part281

#eval (do IO.println s!"p259-row-end 11958 {← IO.monoMsNow}" : IO Unit)

namespace BstLean.Part281
open Real BstLean.Part192 BstLean.Part243

theorem source_rounding11934 :
    (151143681884954229671 / 125000000000000000000000 : ℝ) ≤ world11934.hiddenCharge ∧
    (159231993420417569071919 / 250000000000000000000000 : ℝ) ≤ world11934.frame ∧
    (5543759711 / 500000000000000000 : ℝ) ≤ world11934.moment ∧
    (1472651123493277639422497 / 1000000000000000000000000 : ℝ) ≤ agent11934.frame ∧
    (7251730209567077980737 / 1000000000000000000000000 : ℝ) ≤ agent11934.root ∧
    scalar11934.worldRadius ≤ (2403522599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1273738919893390824139 / 1000000000000000000000000 : ℝ) ≤ agent11934.charge ∧
    (249124487168299015433 / 200000000000000000000000 : ℝ) ≤ scalar11934.upperTail ∧
    (1594673616898227031881 / 1000000000000000000000000 : ℝ) ≤ scalar11934.lowerTail ∧
    scalar11934.totalBudget ≤ (7767999872270947298523 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11934, agent11934, scalar11934] <;> simp only [true_and]

theorem source_rounding11935 :
    (604547848653949907553 / 500000000000000000000000 : ℝ) ≤ world11935.hiddenCharge ∧
    (159228061801686160139171 / 250000000000000000000000 : ℝ) ≤ world11935.frame ∧
    (1385635647 / 125000000000000000 : ℝ) ≤ world11935.moment ∧
    (1472605635098528775793083 / 1000000000000000000000000 : ℝ) ≤ agent11935.frame ∧
    (3625529251243909230929 / 500000000000000000000000 : ℝ) ≤ agent11935.root ∧
    scalar11935.worldRadius ≤ (2403937199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1273464889201504141123 / 1000000000000000000000000 : ℝ) ≤ agent11935.charge ∧
    (1244501721609888751077 / 1000000000000000000000000 : ℝ) ≤ scalar11935.upperTail ∧
    (159334599166506963083 / 100000000000000000000000 : ℝ) ≤ scalar11935.lowerTail ∧
    scalar11935.totalBudget ≤ (7764414504184502071647 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11935, agent11935, scalar11935] <;> simp only [true_and]

theorem source_rounding11936 :
    (1209041954714568834047 / 1000000000000000000000000 : ℝ) ≤ world11936.hiddenCharge ∧
    (159224130863401283169871 / 250000000000000000000000 : ℝ) ≤ world11936.frame ∧
    (11082651677 / 1000000000000000000 : ℝ) ≤ world11936.moment ∧
    (1472560165065979741135429 / 1000000000000000000000000 : ℝ) ≤ agent11936.frame ∧
    (1450077422098874050203 / 200000000000000000000000 : ℝ) ≤ agent11936.root ∧
    scalar11936.worldRadius ≤ (2404351799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (636595565465980612997 / 500000000000000000000000 : ℝ) ≤ agent11936.charge ∧
    (621691114210404020121 / 500000000000000000000000 : ℝ) ≤ scalar11936.upperTail ∧
    (199002464977317238621 / 125000000000000000000000 : ℝ) ≤ scalar11936.lowerTail ∧
    scalar11936.totalBudget ≤ (970104060947353906871 / 125000000000000000000000 : ℝ) := by
  norm_num only [world11936, agent11936, scalar11936] <;> simp only [true_and]

theorem source_rounding11937 :
    (1208988227294033502833 / 1000000000000000000000000 : ℝ) ≤ world11937.hiddenCharge ∧
    (636880802421501147454639 / 1000000000000000000000000 : ℝ) ≤ world11937.frame ∧
    (443208757 / 40000000000000000 : ℝ) ≤ world11937.moment ∧
    (1472514719340783584264881 / 1000000000000000000000000 : ℝ) ≤ agent11937.frame ∧
    (7249715874753555505109 / 1000000000000000000000000 : ℝ) ≤ agent11937.root ∧
    scalar11937.worldRadius ≤ (2404766499999999999999 / 1000000000000000000000000 : ℝ) ∧
    (127291764477829101739 / 100000000000000000000000 : ℝ) ≤ agent11937.charge ∧
    (310565984087257920437 / 250000000000000000000000 : ℝ) ≤ scalar11937.upperTail ∧
    (159069479266808699487 / 100000000000000000000000 : ℝ) ≤ scalar11937.lowerTail ∧
    scalar11937.totalBudget ≤ (242414176067828659783 / 31250000000000000000000 : ℝ) := by
  norm_num only [world11937, agent11937, scalar11937] <;> simp only [true_and]

theorem source_rounding11938 :
    (1208934515040689078357 / 1000000000000000000000000 : ℝ) ≤ world11938.hiddenCharge ∧
    (127373016821936479353381 / 200000000000000000000000 : ℝ) ≤ world11938.frame ∧
    (5538893459 / 500000000000000000 : ℝ) ≤ world11938.moment ∧
    (736234648954475253702069 / 500000000000000000000000 : ℝ) ≤ agent11938.frame ∧
    (3624522437224010677013 / 500000000000000000000000 : ℝ) ≤ agent11938.root ∧
    scalar11938.worldRadius ≤ (2405180999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (254528886086881827501 / 200000000000000000000000 : ℝ) ≤ agent11938.charge ∧
    (620573340940373957089 / 500000000000000000000000 : ℝ) ≤ scalar11938.upperTail ∧
    (63574840482520379199 / 40000000000000000000000 : ℝ) ≤ scalar11938.lowerTail ∧
    scalar11938.totalBudget ≤ (484604878714284401101 / 62500000000000000000000 : ℝ) := by
  norm_num only [world11938, agent11938, scalar11938] <;> simp only [true_and]

theorem source_rounding11939 :
    (604440408974466732079 / 500000000000000000000000 : ℝ) ≤ world11939.hiddenCharge ∧
    (318424684258699416910077 / 500000000000000000000000 : ℝ) ≤ world11939.frame ∧
    (11075355657 / 1000000000000000000 : ℝ) ≤ world11939.moment ∧
    (2944847801513016002313 / 2000000000000000000000 : ℝ) ≤ agent11939.frame ∧
    (1449674821883284700489 / 200000000000000000000000 : ℝ) ≤ agent11939.root ∧
    scalar11939.worldRadius ≤ (2405595599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (636185743797308673213 / 500000000000000000000000 : ℝ) ≤ agent11939.charge ∧
    (1240030682987947418663 / 1000000000000000000000000 : ℝ) ≤ scalar11939.upperTail ∧
    (1588048635069546269487 / 1000000000000000000000000 : ℝ) ≤ scalar11939.lowerTail ∧
    scalar11939.totalBudget ≤ (3875052880172409943107 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11939, agent11939, scalar11939] <;> simp only [true_and]

theorem source_rounding11940 :
    (1208827136013165726589 / 1000000000000000000000000 : ℝ) ≤ world11940.hiddenCharge ∧
    (159208413910975200485419 / 250000000000000000000000 : ℝ) ≤ world11940.frame ∧
    (11072925141 / 1000000000000000000 : ℝ) ≤ world11940.moment ∧
    (736189263934750410972957 / 500000000000000000000000 : ℝ) ≤ agent11940.frame ∧
    (7247703579497597061647 / 1000000000000000000000000 : ℝ) ≤ agent11940.root ∧
    scalar11940.worldRadius ≤ (2406010199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (636049407976801498663 / 500000000000000000000000 : ℝ) ≤ agent11940.charge ∧
    (309728966269638908073 / 250000000000000000000000 : ℝ) ≤ scalar11940.upperTail ∧
    (1586727573953897697621 / 1000000000000000000000000 : ℝ) ≤ scalar11940.lowerTail ∧
    scalar11940.totalBudget ≤ (7746536733002050432003 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11940, agent11940, scalar11940] <;> simp only [true_and]

theorem source_rounding11941 :
    (12087734692277905413 / 10000000000000000000000 : ℝ) ≤ world11941.hiddenCharge ∧
    (127363589097687743960669 / 200000000000000000000000 : ℝ) ≤ world11941.frame ∧
    (11070495371 / 1000000000000000000 : ℝ) ≤ world11941.moment ∧
    (29446663465533711973063 / 20000000000000000000000 : ℝ) ≤ agent11941.frame ∧
    (7247033284530556302623 / 1000000000000000000000000 : ℝ) ≤ agent11941.root ∧
    scalar11941.worldRadius ≤ (2406424799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1271826415206438492527 / 1000000000000000000000000 : ℝ) ≤ agent11941.charge ∧
    (1237802203765415400051 / 1000000000000000000000000 : ℝ) ≤ scalar11941.upperTail ∧
    (158540779676991878987 / 100000000000000000000000 : ℝ) ≤ scalar11941.lowerTail ∧
    scalar11941.totalBudget ≤ (7742970920458481804687 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11941, agent11941, scalar11941] <;> simp only [true_and]

theorem source_rounding11942 :
    (1208719817587213742087 / 1000000000000000000000000 : ℝ) ≤ world11942.hiddenCharge ∧
    (636802238050263478576401 / 1000000000000000000000000 : ℝ) ≤ world11942.frame ∧
    (2213613269 / 200000000000000000 : ℝ) ≤ world11942.moment ∧
    (368071962219754161161389 / 250000000000000000000000 : ℝ) ≤ agent11942.frame ∧
    (905795403044311801193 / 125000000000000000000000 : ℝ) ≤ agent11942.root ∧
    scalar11942.worldRadius ≤ (2406839399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (635777142524290370199 / 500000000000000000000000 : ℝ) ≤ agent11942.charge ∧
    (247337948699496346173 / 200000000000000000000000 : ℝ) ≤ scalar11942.upperTail ∧
    (495027925887620051 / 312500000000000000000 : ℝ) ≤ scalar11942.lowerTail ∧
    scalar11942.totalBudget ≤ (1934852106210542727017 / 250000000000000000000000 : ℝ) := by
  norm_num only [world11942, agent11942, scalar11942] <;> simp only [true_and]

theorem source_rounding11943 :
    (37770818158932572591 / 31250000000000000000000 : ℝ) ≤ world11943.hiddenCharge ∧
    (318393266664313127574071 / 500000000000000000000000 : ℝ) ≤ world11943.frame ∧
    (691602379 / 62500000000000000 : ℝ) ≤ world11943.moment ∧
    (368060637176255125587241 / 250000000000000000000000 : ℝ) ≤ agent11943.frame ∧
    (3622846699404391616807 / 500000000000000000000000 : ℝ) ≤ agent11943.root ∧
    scalar11943.worldRadius ≤ (2407253999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (127128242517587061313 / 100000000000000000000000 : ℝ) ≤ agent11943.charge ∧
    (617789229936932848419 / 500000000000000000000000 : ℝ) ≤ scalar11943.upperTail ∧
    (791386120100791243009 / 500000000000000000000000 : ℝ) ≤ scalar11943.lowerTail ∧
    scalar11943.totalBudget ≤ (966981148690917807083 / 125000000000000000000000 : ℝ) := by
  norm_num only [world11943, agent11943, scalar11943] <;> simp only [true_and]

theorem source_rounding11944 :
    (75538284982380462409 / 62500000000000000000000 : ℝ) ≤ world11944.hiddenCharge ∧
    (159192707830694581671487 / 250000000000000000000000 : ℝ) ≤ world11944.frame ∧
    (11063210527 / 1000000000000000000 : ℝ) ≤ world11944.moment ∧
    (1472197266784298034790251 / 1000000000000000000000000 : ℝ) ≤ agent11944.frame ∧
    (905627975966621630911 / 125000000000000000000000 : ℝ) ≤ agent11944.root ∧
    scalar11944.worldRadius ≤ (2407668599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (635505417642266202671 / 500000000000000000000000 : ℝ) ≤ agent11944.charge ∧
    (1234468328567273623883 / 1000000000000000000000000 : ℝ) ≤ scalar11944.upperTail ∧
    (31629127939579896117 / 20000000000000000000000 : ℝ) ≤ scalar11944.lowerTail ∧
    scalar11944.totalBudget ≤ (3866146579335519655299 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11944, agent11944, scalar11944] <;> simp only [true_and]

theorem source_rounding11945 :
    (241711790695672248431 / 200000000000000000000000 : ℝ) ≤ world11945.hiddenCharge ∧
    (318377566015985708245519 / 500000000000000000000000 : ℝ) ≤ world11945.frame ∧
    (11060783733 / 1000000000000000000 : ℝ) ≤ world11945.moment ∧
    (1472152015016269342003249 / 1000000000000000000000000 : ℝ) ≤ agent11945.frame ∧
    (3622177225483396149437 / 500000000000000000000000 : ℝ) ≤ agent11945.root ∧
    scalar11945.worldRadius ≤ (2408083199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (31768487876779332339 / 25000000000000000000000 : ℝ) ≤ agent11945.charge ∧
    (1233359393925622873689 / 1000000000000000000000000 : ℝ) ≤ scalar11945.upperTail ∧
    (790070946185549147923 / 500000000000000000000000 : ℝ) ≤ scalar11945.lowerTail ∧
    scalar11945.totalBudget ≤ (3864370217107579994137 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11945, agent11945, scalar11945] <;> simp only [true_and]

theorem source_rounding11946 :
    (1208505362361080243057 / 1000000000000000000000000 : ℝ) ≤ world11946.hiddenCharge ∧
    (636739435455457510257753 / 1000000000000000000000000 : ℝ) ≤ world11946.frame ∧
    (2764589421 / 250000000000000000 : ℝ) ≤ world11946.moment ∧
    (1472106781474320468316491 / 1000000000000000000000000 : ℝ) ≤ agent11946.frame ∧
    (7243685328350147367493 / 1000000000000000000000000 : ℝ) ≤ agent11946.root ∧
    scalar11946.worldRadius ≤ (2408497899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1270468464232782796529 / 1000000000000000000000000 : ℝ) ≤ agent11946.charge ∧
    (308062920347884018841 / 250000000000000000000000 : ℝ) ≤ scalar11946.upperTail ∧
    (789414374918105732033 / 500000000000000000000000 : ℝ) ≤ scalar11946.lowerTail ∧
    scalar11946.totalBudget ≤ (309007636285829423913 / 40000000000000000000000 : ℝ) := by
  norm_num only [world11946, agent11946, scalar11946] <;> simp only [true_and]

theorem source_rounding11947 :
    (604225893180331712173 / 500000000000000000000000 : ℝ) ≤ world11947.hiddenCharge ∧
    (63672374159248884639301 / 100000000000000000000000 : ℝ) ≤ world11947.frame ∧
    (11055932377 / 1000000000000000000 : ℝ) ≤ world11947.moment ∧
    (1472061572101128671276159 / 1000000000000000000000000 : ℝ) ≤ agent11947.frame ∧
    (3621508259432727147909 / 500000000000000000000000 : ℝ) ≤ agent11947.root ∧
    scalar11947.worldRadius ≤ (2408912399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1270197682466732236377 / 1000000000000000000000000 : ℝ) ≤ agent11947.charge ∧
    (1231145051204435355023 / 1000000000000000000000000 : ℝ) ≤ scalar11947.upperTail ∧
    (157751680254007718367 / 100000000000000000000000 : ℝ) ≤ scalar11947.lowerTail ∧
    scalar11947.totalBudget ≤ (965205593145436082817 / 125000000000000000000000 : ℝ) := by
  norm_num only [world11947, agent11947, scalar11947] <;> simp only [true_and]

theorem source_rounding11948 :
    (302099556367882741219 / 250000000000000000000000 : ℝ) ≤ world11948.hiddenCharge ∧
    (31835402522115893802457 / 50000000000000000000000 : ℝ) ≤ world11948.frame ∧
    (5526753907 / 500000000000000000 : ℝ) ≤ world11948.moment ∧
    (1472016392838333521148851 / 1000000000000000000000000 : ℝ) ≤ agent11948.frame ∧
    (7242347864051518609101 / 1000000000000000000000000 : ℝ) ≤ agent11948.root ∧
    scalar11948.worldRadius ≤ (2409326999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (317481792367693550159 / 250000000000000000000000 : ℝ) ≤ agent11948.charge ∧
    (1230039629208425938013 / 1000000000000000000000000 : ℝ) ≤ scalar11948.upperTail ∧
    (788103106766740230943 / 500000000000000000000000 : ℝ) ≤ scalar11948.lowerTail ∧
    scalar11948.totalBudget ≤ (96476271999664259491 / 12500000000000000000000 : ℝ) := by
  norm_num only [world11948, agent11948, scalar11948] <;> simp only [true_and]

theorem source_rounding11949 :
    (1208344679688105676971 / 1000000000000000000000000 : ℝ) ≤ world11949.hiddenCharge ∧
    (159173090501049364974041 / 250000000000000000000000 : ℝ) ≤ world11949.frame ∧
    (5525541997 / 500000000000000000 : ℝ) ≤ world11949.moment ∧
    (1471971231760954458759607 / 1000000000000000000000000 : ℝ) ≤ agent11949.frame ∧
    (7241679442907908856959 / 1000000000000000000000000 : ℝ) ≤ agent11949.root ∧
    scalar11949.worldRadius ≤ (2409741599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (634828462471521002547 / 500000000000000000000000 : ℝ) ≤ agent11949.charge ∧
    (614467676219299661881 / 500000000000000000000000 : ℝ) ≤ scalar11949.upperTail ∧
    (1574896896459098702461 / 1000000000000000000000000 : ℝ) ≤ scalar11949.lowerTail ∧
    scalar11949.totalBudget ≤ (3857280980136497291723 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11949, agent11949, scalar11949] <;> simp only [true_and]

theorem source_rounding11950 :
    (604145574502407239897 / 500000000000000000000000 : ℝ) ≤ world11950.hiddenCharge ∧
    (509341341021904523677 / 800000000000000000000 : ℝ) ≤ world11950.frame ∧
    (2762165229 / 250000000000000000 : ℝ) ≤ world11950.moment ∧
    (735963044427998582404971 / 500000000000000000000000 : ℝ) ≤ agent11950.frame ∧
    (3620505627637620348007 / 500000000000000000000000 : ℝ) ≤ agent11950.root ∧
    scalar11950.worldRadius ≤ (2410156199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (634693474291024578751 / 500000000000000000000000 : ℝ) ≤ agent11950.charge ∧
    (613916109759216870547 / 500000000000000000000000 : ℝ) ≤ scalar11950.upperTail ∧
    (786794424934812747177 / 500000000000000000000000 : ℝ) ≤ scalar11950.lowerTail ∧
    scalar11950.totalBudget ≤ (7711025343294588265899 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11950, agent11950, scalar11950] <;> simp only [true_and]

theorem source_rounding11951 :
    (1208237633416083971377 / 1000000000000000000000000 : ℝ) ≤ world11951.hiddenCharge ∧
    (318330496630560406363137 / 500000000000000000000000 : ℝ) ≤ world11951.frame ∧
    (552311929 / 50000000000000000 : ℝ) ≤ world11951.moment ∧
    (367970244004955083050881 / 250000000000000000000000 : ℝ) ≤ agent11951.frame ∧
    (7240343300994306494093 / 1000000000000000000000000 : ℝ) ≤ agent11951.root ∧
    scalar11951.worldRadius ≤ (2410570899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (253823448017337764423 / 200000000000000000000000 : ℝ) ≤ agent11951.charge ∧
    (613365173473453990649 / 500000000000000000000000 : ℝ) ≤ scalar11951.upperTail ∧
    (786141109036041306031 / 500000000000000000000000 : ℝ) ≤ scalar11951.lowerTail ∧
    scalar11951.totalBudget ≤ (7707492011826248220493 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11951, agent11951, scalar11951] <;> simp only [true_and]

theorem source_rounding11952 :
    (1208184132916347801903 / 1000000000000000000000000 : ℝ) ≤ world11952.hiddenCharge ∧
    (159161328238667895286519 / 250000000000000000000000 : ℝ) ≤ world11952.frame ∧
    (5521908493 / 500000000000000000 : ℝ) ≤ world11952.moment ∧
    (735917943641739530218873 / 500000000000000000000000 : ℝ) ≤ agent11952.frame ∧
    (1809918894976518771853 / 250000000000000000000000 : ℝ) ≤ agent11952.root ∧
    scalar11952.worldRadius ≤ (2410985399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1268847799156233285083 / 1000000000000000000000000 : ℝ) ≤ agent11952.charge ∧
    (1225629493445092829109 / 1000000000000000000000000 : ℝ) ≤ scalar11952.upperTail ∧
    (314195342649641727541 / 200000000000000000000000 : ℝ) ≤ scalar11952.lowerTail ∧
    scalar11952.totalBudget ≤ (3851980954353114845659 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11952, agent11952, scalar11952] <;> simp only [true_and]

theorem source_rounding11953 :
    (48325225900001571889 / 40000000000000000000000 : ℝ) ≤ world11953.hiddenCharge ∧
    (318314817678643455391201 / 500000000000000000000000 : ℝ) ≤ world11953.frame ∧
    (11041396133 / 1000000000000000000 : ℝ) ≤ world11953.moment ∧
    (1471790816679097216978923 / 1000000000000000000000000 : ℝ) ≤ agent11953.frame ∧
    (7239008091851691538123 / 1000000000000000000000000 : ℝ) ≤ agent11953.root ∧
    scalar11953.worldRadius ≤ (2411399999999999999999 / 1000000000000000000000000 : ℝ) ∧
    (9910770511643229849 / 7812500000000000000000 : ℝ) ≤ agent11953.charge ∧
    (306132462980323468329 / 250000000000000000000000 : ℝ) ≤ scalar11953.upperTail ∧
    (392418139951505790861 / 250000000000000000000000 : ℝ) ≤ scalar11953.lowerTail ∧
    scalar11953.totalBudget ≤ (7700434977775406175201 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11953, agent11953, scalar11953] <;> simp only [true_and]

theorem source_rounding11954 :
    (1208077177161591464487 / 1000000000000000000000000 : ℝ) ≤ world11954.hiddenCharge ∧
    (636613960468220986588437 / 1000000000000000000000000 : ℝ) ≤ world11954.frame ∧
    (5519488011 / 500000000000000000 : ℝ) ≤ world11954.moment ∧
    (1471745776101506708893387 / 1000000000000000000000000 : ℝ) ≤ agent11954.frame ∧
    (7238340836672476892233 / 1000000000000000000000000 : ℝ) ≤ agent11954.root ∧
    scalar11954.worldRadius ≤ (2411814599999999999999 / 1000000000000000000000000 : ℝ) ∧
    (1268309718789018158331 / 1000000000000000000000000 : ℝ) ≤ agent11954.charge ∧
    (305857848517369398847 / 250000000000000000000000 : ℝ) ≤ scalar11954.upperTail ∧
    (1568369731216568241749 / 1000000000000000000000000 : ℝ) ≤ scalar11954.lowerTail ∧
    scalar11954.totalBudget ≤ (3848455659994013283251 / 500000000000000000000000 : ℝ) := by
  norm_num only [world11954, agent11954, scalar11954] <;> simp only [true_and]

theorem source_rounding11955 :
    (1208023721895445825953 / 1000000000000000000000000 : ℝ) ≤ world11955.hiddenCharge ∧
    (31829914414336413468383 / 50000000000000000000000 : ℝ) ≤ world11955.frame ∧
    (2759139163 / 250000000000000000 : ℝ) ≤ world11955.moment ∧
    (1471700753628984736710679 / 1000000000000000000000000 : ℝ) ≤ agent11955.frame ∧
    (723767381420992793789 / 100000000000000000000000 : ℝ) ≤ agent11955.root ∧
    scalar11955.worldRadius ≤ (2412229199999999999999 / 1000000000000000000000000 : ℝ) ∧
    (9906570927755421489 / 7812500000000000000000 : ℝ) ≤ agent11955.charge ∧
    (611167036518715112287 / 500000000000000000000000 : ℝ) ≤ scalar11955.upperTail ∧
    (62682726627590948477 / 40000000000000000000000 : ℝ) ≤ scalar11955.lowerTail ∧
    scalar11955.totalBudget ≤ (4808369267351409587 / 625000000000000000000 : ℝ) := by
  norm_num only [world11955, agent11955, scalar11955] <;> simp only [true_and]

theorem source_rounding11956 :
    (241594056339208421689 / 200000000000000000000000 : ℝ) ≤ world11956.hiddenCharge ∧
    (636582618812063535264511 / 1000000000000000000000000 : ℝ) ≤ world11956.frame ∧
    (5517069011 / 500000000000000000 : ℝ) ≤ world11956.moment ∧
    (1471655755201991191014823 / 1000000000000000000000000 : ℝ) ≤ agent11956.frame ∧
    (289480280972228678561 / 40000000000000000000000 : ℝ) ≤ agent11956.root ∧
    scalar11956.worldRadius ≤ (2412643799999999999999 / 1000000000000000000000000 : ℝ) ∧
    (316943176270536060451 / 250000000000000000000000 : ℝ) ≤ agent11956.charge ∧
    (610618955066346527047 / 500000000000000000000000 : ℝ) ≤ scalar11956.upperTail ∧
    (782883945940326724969 / 500000000000000000000000 : ℝ) ≤ scalar11956.lowerTail ∧
    scalar11956.totalBudget ≤ (1537974710024414294711 / 200000000000000000000000 : ℝ) := by
  norm_num only [world11956, agent11956, scalar11956] <;> simp only [true_and]

theorem source_rounding11957 :
    (241583371311565120443 / 200000000000000000000000 : ℝ) ≤ world11957.hiddenCharge ∧
    (318283476021740913939183 / 500000000000000000000000 : ℝ) ≤ world11957.frame ∧
    (11031720133 / 1000000000000000000 : ℝ) ≤ world11957.moment ∧
    (1471610780806860005025331 / 1000000000000000000000000 : ℝ) ≤ agent11957.frame ∧
    (7236340466801691519373 / 1000000000000000000000000 : ℝ) ≤ agent11957.root ∧
    scalar11957.worldRadius ≤ (2413058399999999999999 / 1000000000000000000000000 : ℝ) ∧
    (253500919495705787541 / 200000000000000000000000 : ℝ) ≤ agent11957.charge ∧
    (61007145196985308247 / 50000000000000000000000 : ℝ) ≤ scalar11957.upperTail ∧
    (1564468908291420839739 / 1000000000000000000000000 : ℝ) ≤ scalar11957.lowerTail ∧
    scalar11957.totalBudget ≤ (1921589870804146139561 / 250000000000000000000000 : ℝ) := by
  norm_num only [world11957, agent11957, scalar11957] <;> simp only [true_and]

theorem source_rounding11958 :
    (241572689295047961217 / 200000000000000000000000 : ℝ) ≤ world11958.hiddenCharge ∧
    (636551287980238431377063 / 1000000000000000000000000 : ℝ) ≤ world11958.frame ∧
    (1378662873 / 125000000000000000 : ℝ) ≤ world11958.moment ∧
    (183945728803742747174047 / 125000000000000000000000 : ℝ) ≤ agent11958.frame ∧
    (7235674141539874171843 / 1000000000000000000000000 : ℝ) ≤ agent11958.root ∧
    scalar11958.worldRadius ≤ (2413472899999999999999 / 1000000000000000000000000 : ℝ) ∧
    (63361837782169193791 / 50000000000000000000000 : ℝ) ≤ agent11958.charge ∧
    (304762245270838298191 / 250000000000000000000000 : ℝ) ≤ scalar11958.upperTail ∧
    (781585564244207954351 / 500000000000000000000000 : ℝ) ≤ scalar11958.lowerTail ∧
    scalar11958.totalBudget ≤ (7682848622221036851821 / 1000000000000000000000000 : ℝ) := by
  norm_num only [world11958, agent11958, scalar11958] <;> simp only [true_and]

noncomputable def paperAgent11934 : AgentParameters :=
  { agent11934 with charge := (1273738923 / 1000000000000 : ℝ) }

theorem agent_is_repriced11934 : agent11934 =
    BstLean.Part265.agentRepriced 11934 world11934 paperAgent11934 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11934, agent11934]

noncomputable def paperAgent11935 : AgentParameters :=
  { agent11935 with charge := (318366223 / 250000000000 : ℝ) }

theorem agent_is_repriced11935 : agent11935 =
    BstLean.Part265.agentRepriced 11935 world11935 paperAgent11935 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11935, agent11935]

noncomputable def paperAgent11936 : AgentParameters :=
  { agent11936 with charge := (636595567 / 500000000000 : ℝ) }

theorem agent_is_repriced11936 : agent11936 =
    BstLean.Part265.agentRepriced 11936 world11936 paperAgent11936 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11936, agent11936]

noncomputable def paperAgent11937 : AgentParameters :=
  { agent11937 with charge := (79557353 / 62500000000 : ℝ) }

theorem agent_is_repriced11937 : agent11937 =
    BstLean.Part265.agentRepriced 11937 world11937 paperAgent11937 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11937, agent11937]

noncomputable def paperAgent11938 : AgentParameters :=
  { agent11938 with charge := (636322217 / 500000000000 : ℝ) }

theorem agent_is_repriced11938 : agent11938 =
    BstLean.Part265.agentRepriced 11938 world11938 paperAgent11938 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11938, agent11938]

noncomputable def paperAgent11939 : AgentParameters :=
  { agent11939 with charge := (1272371491 / 1000000000000 : ℝ) }

theorem agent_is_repriced11939 : agent11939 =
    BstLean.Part265.agentRepriced 11939 world11939 paperAgent11939 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11939, agent11939]

noncomputable def paperAgent11940 : AgentParameters :=
  { agent11940 with charge := (1272098819 / 1000000000000 : ℝ) }

theorem agent_is_repriced11940 : agent11940 =
    BstLean.Part265.agentRepriced 11940 world11940 paperAgent11940 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11940, agent11940]

noncomputable def paperAgent11941 : AgentParameters :=
  { agent11941 with charge := (635913209 / 500000000000 : ℝ) }

theorem agent_is_repriced11941 : agent11941 =
    BstLean.Part265.agentRepriced 11941 world11941 paperAgent11941 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11941, agent11941]

noncomputable def paperAgent11942 : AgentParameters :=
  { agent11942 with charge := (79472143 / 62500000000 : ℝ) }

theorem agent_is_repriced11942 : agent11942 =
    BstLean.Part265.agentRepriced 11942 world11942 paperAgent11942 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11942, agent11942]

noncomputable def paperAgent11943 : AgentParameters :=
  { agent11943 with charge := (1271282429 / 1000000000000 : ℝ) }

theorem agent_is_repriced11943 : agent11943 =
    BstLean.Part265.agentRepriced 11943 world11943 paperAgent11943 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11943, agent11943]

noncomputable def paperAgent11944 : AgentParameters :=
  { agent11944 with charge := (1271010839 / 1000000000000 : ℝ) }

theorem agent_is_repriced11944 : agent11944 =
    BstLean.Part265.agentRepriced 11944 world11944 paperAgent11944 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11944, agent11944]

noncomputable def paperAgent11945 : AgentParameters :=
  { agent11945 with charge := (1270739519 / 1000000000000 : ℝ) }

theorem agent_is_repriced11945 : agent11945 =
    BstLean.Part265.agentRepriced 11945 world11945 paperAgent11945 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11945, agent11945]

noncomputable def paperAgent11946 : AgentParameters :=
  { agent11946 with charge := (317617117 / 250000000000 : ℝ) }

theorem agent_is_repriced11946 : agent11946 =
    BstLean.Part265.agentRepriced 11946 world11946 paperAgent11946 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11946, agent11946]

noncomputable def paperAgent11947 : AgentParameters :=
  { agent11947 with charge := (254039537 / 200000000000 : ℝ) }

theorem agent_is_repriced11947 : agent11947 =
    BstLean.Part265.agentRepriced 11947 world11947 paperAgent11947 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11947, agent11947]

noncomputable def paperAgent11948 : AgentParameters :=
  { agent11948 with charge := (317481793 / 250000000000 : ℝ) }

theorem agent_is_repriced11948 : agent11948 =
    BstLean.Part265.agentRepriced 11948 world11948 paperAgent11948 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11948, agent11948]

noncomputable def paperAgent11949 : AgentParameters :=
  { agent11949 with charge := (39676779 / 31250000000 : ℝ) }

theorem agent_is_repriced11949 : agent11949 =
    BstLean.Part265.agentRepriced 11949 world11949 paperAgent11949 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11949, agent11949]

noncomputable def paperAgent11950 : AgentParameters :=
  { agent11950 with charge := (158673369 / 125000000000 : ℝ) }

theorem agent_is_repriced11950 : agent11950 =
    BstLean.Part265.agentRepriced 11950 world11950 paperAgent11950 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11950, agent11950]

noncomputable def paperAgent11951 : AgentParameters :=
  { agent11951 with charge := (1269117243 / 1000000000000 : ℝ) }

theorem agent_is_repriced11951 : agent11951 =
    BstLean.Part265.agentRepriced 11951 world11951 paperAgent11951 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11951, agent11951]

noncomputable def paperAgent11952 : AgentParameters :=
  { agent11952 with charge := (634423901 / 500000000000 : ℝ) }

theorem agent_is_repriced11952 : agent11952 =
    BstLean.Part265.agentRepriced 11952 world11952 paperAgent11952 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11952, agent11952]

noncomputable def paperAgent11953 : AgentParameters :=
  { agent11953 with charge := (317144657 / 250000000000 : ℝ) }

theorem agent_is_repriced11953 : agent11953 =
    BstLean.Part265.agentRepriced 11953 world11953 paperAgent11953 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11953, agent11953]

noncomputable def paperAgent11954 : AgentParameters :=
  { agent11954 with charge := (634154861 / 500000000000 : ℝ) }

theorem agent_is_repriced11954 : agent11954 =
    BstLean.Part265.agentRepriced 11954 world11954 paperAgent11954 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11954, agent11954]

noncomputable def paperAgent11955 : AgentParameters :=
  { agent11955 with charge := (634020541 / 500000000000 : ℝ) }

theorem agent_is_repriced11955 : agent11955 =
    BstLean.Part265.agentRepriced 11955 world11955 paperAgent11955 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11955, agent11955]

noncomputable def paperAgent11956 : AgentParameters :=
  { agent11956 with charge := (316943177 / 250000000000 : ℝ) }

theorem agent_is_repriced11956 : agent11956 =
    BstLean.Part265.agentRepriced 11956 world11956 paperAgent11956 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11956, agent11956]

noncomputable def paperAgent11957 : AgentParameters :=
  { agent11957 with charge := (6337523 / 5000000000 : ℝ) }

theorem agent_is_repriced11957 : agent11957 =
    BstLean.Part265.agentRepriced 11957 world11957 paperAgent11957 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11957, agent11957]

noncomputable def paperAgent11958 : AgentParameters :=
  { agent11958 with charge := (1267236759 / 1000000000000 : ℝ) }

theorem agent_is_repriced11958 : agent11958 =
    BstLean.Part265.agentRepriced 11958 world11958 paperAgent11958 BstLean.Part265.chargeFloor := by
  norm_num [BstLean.Part265.agentRepriced, BstLean.Part265.chargeFloor,
    paperAgent11958, agent11958]

end BstLean.Part281
