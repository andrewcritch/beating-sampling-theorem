import BstLean.Part252Scalar
import BstLean.Part169Var

/-! The pointwise variance budget follows from ordinary matrix operator bounds. -/
namespace BstLean.Part252
open MeasureTheory Real
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part162 (psiA)
open BstLean.Part53 (unitF53)
open BstLean.Part29 (stdGauss)

theorem variance_pointwise {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (hb : normSq (bR c) ≠ 0) {O₁ O₂ : ℝ}
    (h1 : OpB (A1 c) O₁) (h2 : OpB (A2 c) O₂)
    (hO1 : 0 ≤ O₁) (hO2 : 0 ≤ O₂) (a : Ix n) :
    0 ≤ VR c a ∧ VR c a ≤ 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 / ((n : ℝ) - 2) := by
  have hn1 : 1 ≤ n := by omega
  have hL := fX_euLip hn1 c h1 h2 hO1 hO2
  have hL0 : 0 ≤ O₂ * O₁ / √(n : ℝ) := by positivity
  have hs := BstLean.Part162.latC_sq_le (paperDesignP n) c a
  obtain ⟨i1, i2⟩ := int_fX_lat hn1 c hs
  have hV := VR_eq hn1 c hb a
  rw [fbR_eq] at hV
  unfold fbarS at hV
  have hvar := var_eq i1 i2
  rw [← hvar] at hV
  have hidx := BstLean.Part162.idx_var_psi (by omega) (paperDesignP n) c hL0 hL
    (fun t x ht => fX_hom c t x ht) a
  have hpsi : ∫ v, psiA (fX c) (paperDesignP n) c a v ∂stdGauss (Fin (n - 1)) ≤
      2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 := by
    have hb' := fun v => BstLean.Part162.psiA_bounds (by omega) (paperDesignP n) c hL0 hL
      (fun t x ht => fX_hom c t x ht) a v
    have mP := BstLean.Part162.meas_psi_v (hL.continuous hL0) (paperDesignP n) c a
    calc _ ≤ ∫ _v, 2 * (O₂ * O₁ / √(n : ℝ)) ^ 2 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (Integrable.mono' (integrable_const _) mP.aestronglyMeasurable
            (Filter.Eventually.of_forall fun v => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hb' v).1]; exact (hb' v).2))
            (integrable_const _) fun v => (hb' v).2
      _ = _ := by simp
  have h2n : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine ⟨?_, ?_⟩
  · rw [hV]; exact integral_nonneg fun v => sq_nonneg _
  · rw [hV]
    refine hidx.trans ?_
    exact div_le_div_of_nonneg_right hpsi h2n.le

theorem variance_pointwise_row (c : Ret 12225) (hb : normSq (bR c) ≠ 0)
    (h1 : OpB (A1 c) 160) (h2 : OpB (A2 c) (283 / 100)) (a : Ix 12225) :
    |VR c a| ≤ varianceMax := by
  have h := variance_pointwise (by norm_num) c hb h1 h2 (by norm_num) (by norm_num) a
  rw [abs_of_nonneg h.1]
  refine h.2.trans ?_
  norm_num only [Nat.cast_ofNat]
  rw [div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 12225)]
  norm_num [varianceMax]

end BstLean.Part252
