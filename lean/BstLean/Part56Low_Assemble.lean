import BstLean.Part56Low_Integration
import BstLean.Part50Laws

namespace BstLean.Part56.LowAssemble

open MeasureTheory BstLean.Part29 BstLean.Part36 BstLean.Part41 BstLean.Part53
open LowIntegration LowCoefficients LowScale

lemma propLow56_of_angular (d k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d)
    (C a : ℝ) (ha : 0 < a) (n0 : ℕ) (hn0 : 1 ≤ n0)
    (hAngular : ∀ n : ℕ, n0 ≤ n → ∀ v : Fin n → ℝ, UnitV v →
      ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
      a ≤ ∫ x, (1 - (∑ i, x i * v i) ^ 2) ^ k ∂lawRK n t v) :
    ∃ cL : ℝ, 0 < cL ∧ PropLow56 d k C cL n0 := by
  let B : ℝ := (k + 1 : ℝ) ^ 3 * weightBound d k
  have hB : 0 < B := mul_pos (by positivity) (weightBound_pos d k)
  refine ⟨a / B, div_pos ha hB, ?_⟩
  intro n hn v hv t ht htC f0 T hT
  have hn1 : 1 ≤ n := hn0.trans hn
  have hμ := (BstLean.Part50.binghamA_antipodal hn1 (rk1 t v)).sph
  have h := integrated_coefficient_lower (d := d) hμ k hn1 (hk.trans hkd) f0 T hT v hv
  have hm := hAngular n hn v hv t ht htC
  have hnSum : normSum k (scaleT (sg n d) (TF k f0 T)) =
      ∑ j ∈ Finset.Icc 1 k, frob (T j) / DD n d ^ j := by
    unfold normSum
    apply Finset.sum_congr rfl
    intro j hj
    exact normalized_frob d k j hn1 (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 f0 T
  have hl := mul_le_mul_of_nonneg_right hm (normSum_nonneg k (scaleT (sg n d) (TF k f0 T)))
  rw [hnSum] at h hl
  have hnPow : 0 < (n : ℝ) ^ ((k - 1) / 2) := pow_pos (by exact_mod_cast hn1) _
  apply (div_le_iff₀ hnPow).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hB).mpr
  have hfin := hl.trans h
  dsimp only [B, lawRK] at *
  convert hfin using 1 <;> ring


end BstLean.Part56.LowAssemble
