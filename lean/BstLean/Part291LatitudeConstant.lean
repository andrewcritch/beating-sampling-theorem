import BstLean.Part291LatitudeNumerics
import BstLean.Part212FreshEvent

namespace BstLean.BlueprintLow
open Real MeasureTheory BstLean.Part130 BstLean.Part212

theorem latitude_frobenius_band {n : ℕ} (hn : 8000 ≤ n) :
    2 / (mA n : ℝ) * frobEnvelopeSquared160 n ≤ 2.002 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : (0 : ℝ) < mA n := by unfold mA; positivity
  have hnm : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
  unfold frobEnvelopeSquared160
  rw [hnm]
  field_simp
  nlinarith

theorem latitude_transverse_band {n : ℕ} (hn : 8000 ≤ n) :
    transverseConstant160 * √(2 / (mA n : ℝ)) * operatorEnvelope160 n ≤ 0.181065 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsN : (89.442719 : ℝ) ≤ √(n : ℝ) := le_sqrt_of_sq_le (by linarith)
  have hs0 : 0 < √(n : ℝ) := sqrt_pos.mpr hn0
  have hm : (mA n : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; rfl
  have hs2 : √(2 : ℝ) ≤ 1.414214 := sqrt_le_iff.mpr (by norm_num)
  have hg := BstLean.Part252.gaussian80_le
  have hg0 := BstLean.Part152.gaussMomConst_nonneg 80
  unfold transverseConstant160 operatorEnvelope160
  rw [hm, sqrt_div (by norm_num : (0 : ℝ) ≤ 2), sqrt_sq hn0.le,
    sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 8 * (1.414214 / (n : ℝ)) * (1.414214 / √(n : ℝ) * ((n : ℝ) + √(n : ℝ) + 8)) := by gcongr
    _ = 8 * (1.414214 : ℝ) ^ 2 * (1 / √(n : ℝ) + 1 / n + 8 / (n * √(n : ℝ))) := by
      field_simp <;> ring
    _ ≤ 8 * (1.414214 : ℝ) ^ 2 * (1 / 89.442719 + 1 / 8000 + 8 / (8000 * 89.442719)) := by gcongr
    _ ≤ (0.181065 : ℝ) := by norm_num

theorem latitude_jacobian_band {n : ℕ} (hn : 8000 ≤ n) :
    jacobianConstantSquared160 n 2.254 (frobEnvelopeSquared160 n) ≤ 5.036 := by
  have hF := latitude_frobenius_band hn
  have hZ := latitude_transverse_band hn
  have hf0 := (frobEnvelope_pos160 (by omega : 2 ≤ n)).le
  have hz0 := (transverseConstant_pos160).le
  have hop0 := (operatorEnvelope_pos160 (by omega : 1 ≤ n)).le
  have hs : √(2.254 + 2 / (mA n : ℝ) * frobEnvelopeSquared160 n) ≤ 2.06301 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold jacobianConstantSquared160
  calc
    _ ≤ ((2.06301 : ℝ) + 0.181065) ^ 2 := by gcongr
    _ ≤ (5.036 : ℝ) := by norm_num

theorem latitude_coefficient_band {n : ℕ} (hn : 8000 ≤ n) :
    latitudeCoefficient n 12 0.528 ≤ 0.53274 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hden : (0.9967 : ℝ) ≤ 1 - 50 * 0.528 / n := by
    have h : (50 * 0.528 : ℝ) / n ≤ (50 * 0.528 : ℝ) / 8000 := by gcongr
    linarith
  have hR : (0.528 : ℝ) / (1 - 50 * 0.528 / n) ≤ 0.52975 := by
    calc
      _ ≤ (0.528 : ℝ) / 0.9967 := by gcongr
      _ ≤ (0.52975 : ℝ) := by norm_num
  unfold latitudeCoefficient inverseLatitudeCoefficient
  norm_num only [Nat.cast_ofNat] at hR ⊢
  rw [show (66 / 125 : ℝ) / (1 - (132 / 5) / n) * ((n : ℝ) + 48 - 3) / n =
    (66 / 125 : ℝ) / (1 - (132 / 5) / n) * (1 + 45 / n) by field_simp <;> ring]
  calc
    _ ≤ (2119 / 4000 : ℝ) * (1 + 45 / 8000) := by gcongr
    _ ≤ (26637 / 50000 : ℝ) := by norm_num

theorem latitude_charge_factor : (20000 : ℝ) ^ (1 / 80 : ℝ) ≤ 1.132 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (80 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1.132)
  have he := rpow_inv_natCast_pow (x := (20000 : ℝ)) (n := 80) (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at he
  rw [he]
  norm_num

theorem latitude_constant_band {n : ℕ} (hn : 8000 ≤ n) :
    latitudeConstant (√(5.036 : ℝ)) (latitudeCoefficient n 12 0.528) (1 / 10000) ≤ 3.042 := by
  have hc := latitude_coefficient_band hn
  have hfac := latitude_charge_factor
  unfold latitudeConstant
  rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 5.036)]
  rw [show (2 : ℝ) / (1 / 10000) = 20000 by norm_num]
  have hc0 : 0 ≤ latitudeCoefficient n 12 0.528 := by
    have hnr : (8000 : ℝ) ≤ n := by exact_mod_cast hn
    have hden : 0 < 1 - (50 * 0.528 : ℝ) / n := by
      have h : (50 * 0.528 : ℝ) / n ≤ (50 * 0.528 : ℝ) / 8000 := by gcongr
      linarith
    unfold latitudeCoefficient inverseLatitudeCoefficient
    norm_num only [Nat.cast_ofNat] at hden ⊢
    exact div_nonneg (mul_nonneg (div_nonneg (by norm_num) hden.le) (by linarith)) (Nat.cast_nonneg n)
  calc
    _ ≤ (1.132 : ℝ) * 5.036 * 0.53274 := by gcongr
    _ ≤ (3.042 : ℝ) := by norm_num

end BstLean.BlueprintLow
