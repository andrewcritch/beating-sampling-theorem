import BstLean.Part218Event
import BstLean.Part218NormDecomposition

/-! The concrete first-layer event supplies the deterministic World bounds. -/
namespace BstLean.Part218
open MeasureTheory Real
open BstLean.Part130 BstLean.Part133 BstLean.Part137 BstLean.Part205 BstLean.Part214

noncomputable def e1FrobBound (N m : ℕ) (ε : Fin 4 → ℝ) : ℝ :=
  √((1 + ε 0) * ((m : ℝ) * N * (m + N + 1)) / (4 * (N : ℝ) ^ 4)) +
  √((1 / (4 * (N : ℝ)) - cN N ^ 2) ^ 2 * (4 / (N : ℝ) ^ 2) *
    ((1 + ε 1) * ((m : ℝ) * N * (N + 2))) + (1 + ε 2) * covarianceMeanBound N m)
noncomputable def e1InputVarianceBound (N m : ℕ) (ε : Fin 4 → ℝ) : ℝ :=
  (1 + ε 1 + ε 3) * inputVarianceMean N m
noncomputable def e1EnergyLower (N m : ℕ) (εω : ℝ) : ℝ := (1 - εω) * (m : ℝ) / N

lemma diagonalSum_paper {N m : ℕ} (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ) :
    diagonalSum N m M = (4 / (N : ℝ) ^ 2) * BstLean.Part214.paperDiagonal N m M := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold BstLean.Part214.paperDiagonal
  field_simp

theorem e1_worldFrob {N m : ℕ} (hN : 1 ≤ N) {M : Matrix (Fin m) (Fin N) ℝ}
    {εω ph : ℝ} {ε : Fin 4 → ℝ} (hM : M ∈ concreteFirstLayerEvent N m εω ph ε) :
    worldFrobSq M ≤ e1FrobBound N m ε ^ 2 := by
  obtain ⟨hω, hS, hB, hC, hH, hV⟩ := (concreteFirstLayerEvent_iff M εω ph ε).mp hM
  have hR : remainderFrobSq M ≤
      (1 / (4 * (N : ℝ)) - cN N ^ 2) ^ 2 * (4 / (N : ℝ) ^ 2) *
        ((1 + ε 1) * ((m : ℝ) * N * (N + 2))) + (1 + ε 2) * covarianceMeanBound N m := by
    rw [remainderFrob_split hN, diagonalSum_paper hN]
    have h := mul_le_mul_of_nonneg_left hB
      (show 0 ≤ (1 / (4 * (N : ℝ)) - cN N ^ 2) ^ 2 * (4 / (N : ℝ) ^ 2) by positivity)
    nlinarith
  exact worldFrob_bound hN M hS hR

theorem e1_worldInputVariance {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    {M : Matrix (Fin m) (Fin N) ℝ} {εω ph : ℝ} {ε : Fin 4 → ℝ}
    (hM : M ∈ concreteFirstLayerEvent N m εω ph ε) :
    worldInputVariance M ≤ e1InputVarianceBound N m ε := by
  obtain ⟨hω, hS, hB, hC, hH, hV⟩ := (concreteFirstLayerEvent_iff M εω ph ε).mp hM
  rw [worldInputVariance_split hN hm, diagonalSum_paper hN]
  have hd := normDiagonal_nonneg hN
  have h := mul_le_mul_of_nonneg_left hB
    (show 0 ≤ normDiagonal N * (4 / (N : ℝ) ^ 2) by positivity)
  have he : normDiagonal N * (4 / (N : ℝ) ^ 2) *
      ((1 + ε 1) * ((m : ℝ) * N * (N + 2))) = (1 + ε 1) * inputVarianceMean N m := by
    rw [← normDiagonal_mean (m := m) hN]
    ring
  rw [he] at h
  unfold e1InputVarianceBound
  nlinarith

theorem e1_worldMean {n m : ℕ} (hn : 4096 ≤ n) (hm : 1 ≤ m)
    {M : Matrix (Fin m) (Fin (2 * n)) ℝ} {εω ph : ℝ} {ε : Fin 4 → ℝ}
    (hεω : εω < 1) (hM : M ∈ concreteFirstLayerEvent (2 * n) m εω ph ε) :
    meanBound (2 * (2 * n : ℕ) * cN (2 * n) ^ 2) (worldT M) (worldNu M) ≤
      meanBound (2 * (2 * n : ℕ) * cN (2 * n) ^ 2)
        ((e1FrobBound (2 * n) m ε ^ 2 + 2 * (directionMean (2 * n) m / ph)) /
          e1EnergyLower (2 * n) m εω ^ 2)
        (√(e1InputVarianceBound (2 * n) m ε) / e1EnergyLower (2 * n) m εω) := by
  have hN : 1 ≤ 2 * n := by omega
  have hn' : (0 : ℝ) < (2 * n : ℕ) := by exact_mod_cast hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hq : 0 < e1EnergyLower (2 * n) m εω := by unfold e1EnergyLower; positivity
  have hω := ((concreteFirstLayerEvent_iff M εω ph ε).mp hM).1
  have hQ := energy_window hN hm M hεω hω
  have hH := ((concreteFirstLayerEvent_iff M εω ph ε).mp hM).2.2.2.2.1
  have h := world_mean_from_stats hn M hq hQ.2.1 (e1_worldFrob hN hM) hH
    (e1_worldInputVariance hN hm hM) hm
  rwa [world_ratio hN hm M hQ.1] at h

end BstLean.Part218
#print axioms BstLean.Part218.e1_worldFrob
#print axioms BstLean.Part218.e1_worldInputVariance
#print axioms BstLean.Part218.e1_worldMean
