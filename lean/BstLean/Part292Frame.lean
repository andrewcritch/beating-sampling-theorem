import BstLean.Part292FirstLayer

/-! The retained-frame admissibility condition supplies the order-1664 bound. -/
namespace BstLean.Part292
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part167 BstLean.Part223
open BstLean.Part172 (fr_orth fr_xLat)
open BstLean.Part161 (uHat xLat)
open BstLean.Part162 (dirW)
open BstLean.Part53 (unitF53)

theorem admissible_first_layer1664 {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    {u w : Fin n → ℝ} {s cs : ℝ}
    (hu : normSq u = 1) (hw : normSq w = 1) (huw : ∑ i, u i * w i = 0)
    (hsc : s ^ 2 + cs ^ 2 = 1)
    (C : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ)
    (hC : ∀ A, normSq (C A) ≤ 1)
    (hadm : ∀ A A' : Matrix (Fin (mA n)) (Fin n) ℝ,
      A *ᵥ (s • u + cs • w) = A' *ᵥ (s • u + cs • w) →
      A *ᵥ u = A' *ᵥ u → (∀ i, ∑ j, A i j ^ 2 = ∑ j, A' i j ^ 2) → C A = C A') :
    (∫⁻ A, ENNReal.ofReal (latSq (vecMul (C A) (D1A1 A (s • u + cs • w))) u w ^ 832)
      ∂gaussMat (mA n) n (2 / (n : ℝ))) ≤
      ENNReal.ofReal ((24933 / 10000 : ℝ) ^ 832) := by
  apply first_layer_moment1664_band hn hn' hu hw huw hsc C hC
  intro W W' h
  have hn2 : 2 ≤ n := by omega
  have hγ : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  have fr := frame_reads (m := mA n) hn2 hu hw huw hsc hγ W
  have fr' := frame_reads (m := mA n) hn2 hu hw huw hsc hγ W'
  apply hadm
  · funext i
    rw [(fr i).1, (fr' i).1, (h i).1]
  · funext i
    rw [(fr i).2.1, (fr' i).2.1, (h i).1, (h i).2.1]
  · intro i
    rw [(fr i).2.2, (fr' i).2.2, (h i).1, (h i).2.1, (h i).2.2]

theorem latitude_first_layer1664 {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    {c : Ret n} (hc : c.1.2 ≠ 0) {s : ℝ} (hs : s ^ 2 ≤ 1)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0)
    (C : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ)
    (hC : ∀ A, normSq (C A) ≤ 1)
    (hadm : ∀ A A' : Matrix (Fin (mA n)) (Fin n) ℝ,
      A *ᵥ xLat c s (unitF53 v) = A' *ᵥ xLat c s (unitF53 v) →
      A *ᵥ uHat c = A' *ᵥ uHat c →
      (∀ i, ∑ j, A i j ^ 2 = ∑ j, A' i j ^ 2) → C A = C A') :
    (∫⁻ A, ENNReal.ofReal (latSq (vecMul (C A) (D1A1 A (xLat c s (unitF53 v))))
      (uHat c) (dirW c (unitF53 v)) ^ 832) ∂gaussMat (mA n) n (2 / (n : ℝ))) ≤
      ENNReal.ofReal ((24933 / 10000 : ℝ) ^ 832) := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hu, hw, huw⟩ := fr_orth hn1 hc hv
  have hsc : s ^ 2 + √(1 - s ^ 2) ^ 2 = 1 := by rw [Real.sq_sqrt (by linarith)]; ring
  rw [fr_xLat hn1 hc] at hadm ⊢
  exact admissible_first_layer1664 hn hn' hu hw huw hsc C hC hadm

end BstLean.Part292
