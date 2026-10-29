import BstLean.Part253Ideal
import BstLean.Part291DirectionError

namespace BstLean.BlueprintLow
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part219 BstLean.Part215

theorem directionRadius8000 {θ b R : ℝ} (j : ℕ) (hθ : 0 ≤ θ) (hb : θ ≤ b)
    (hd : 0 < 1 - (2 * j + 2 : ℝ) * b / 8000)
    (hR : b / (1 - (2 * j + 2 : ℝ) * b / 8000) ≤ R) :
    radiusCoefficient 8000 j θ ≤ R := by
  unfold radiusCoefficient
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hR
  apply div_le_div₀ (hθ.trans hb) hb hd
  have hj : (0 : ℝ) ≤ 2 * j + 2 := by positivity
  nlinarith

theorem directionAmplitude8000 {θ a b A : ℝ} (ha : a ≤ θ) (hb : θ ≤ b) (hb1 : b ≤ 1)
    (hd : 0 < 1 - 4 * b / 8000) (hA0 : 0 ≤ A)
    (hA : (1 - a) / (1 - 4 * b / 8000) ≤ A ^ 2) :
    paperAmplitude 8000 θ ≤ A := by
  unfold paperAmplitude
  apply sqrt_le_iff.mpr
  refine ⟨hA0, ?_⟩
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hA
  apply div_le_div₀ (by linarith : 0 ≤ 1 - a) (by linarith) hd
  linarith

theorem directionIdeal8000_from_bounds {θ e A K R1 R4 R24 R48 R96 T : ℝ}
    (hθ : 0 ≤ θ) (he : 0.665 ≤ e) (hT : θ ≤ T) (hT0 : 0 ≤ T) (hT1 : T ≤ 0.54)
    (hA0 : 0 ≤ A) (hK0 : 0 ≤ K)
    (hA : paperAmplitude 8000 θ ≤ A) (hK : kernelSlope (1 - θ) ≤ K)
    (h1 : radiusCoefficient 8000 1 θ ≤ R1)
    (h4 : radiusCoefficient 8000 4 θ ≤ R4)
    (h24 : radiusCoefficient 8000 24 θ ≤ R24)
    (h48 : radiusCoefficient 8000 48 θ ≤ R48)
    (h96 : radiusCoefficient 8000 96 θ ≤ R96)
    (hR1 : 0 ≤ R1) (hR4 : 0 ≤ R4) (hR24 : 0 ≤ R24)
    (hR48 : 0 ≤ R48) (hR96 : 0 ≤ R96)
    (hscalar : K * A * R48 * 1.002934 / 0.815475 +
      (77 / 100 : ℝ) * √R24 / 0.815475 *
        (√(R1 / 8000) + A * 6.7 * R96 * 1.005921 / 89.442719 +
          2 * ((T + √T * R4 * 1.000188) / 8000)) ≤ 0.235) :
    paperIdeal 8000 θ e ≤ 0.235 := by
  have hsE : (0.815475 : ℝ) ≤ √e := le_sqrt_of_sq_le (by linarith)
  have hsN : (89.442719 : ℝ) ≤ √8000 := le_sqrt_of_sq_le (by norm_num)
  have h47 : √(1 + 47 / (8000 : ℝ)) ≤ 1.002934 := sqrt_le_iff.mpr (by norm_num)
  have h95 : √(1 + 95 / (8000 : ℝ)) ≤ 1.005921 := sqrt_le_iff.mpr (by norm_num)
  have h3 : √(1 + 3 / (8000 : ℝ)) ≤ 1.000188 := sqrt_le_iff.mpr (by norm_num)
  have hr := BstLean.Part253.rotation24_upper
  have hrad (j : ℕ) (hj : j ≤ 96) : 0 ≤ radiusCoefficient 8000 j θ := by
    unfold radiusCoefficient
    have hjR : (j : ℝ) ≤ 96 := by exact_mod_cast hj
    have hjc : (2 * j + 2 : ℝ) ≤ 194 := by linarith
    have hp := mul_le_mul hjc (hT.trans hT1) hθ (by norm_num : (0 : ℝ) ≤ 194)
    apply div_nonneg hθ
    simp only [Nat.cast_ofNat]
    nlinarith
  have hr1 := hrad 1 (by norm_num)
  have hr4 := hrad 4 (by norm_num)
  have hr24 := hrad 24 (by norm_num)
  have hr48 := hrad 48 (by norm_num)
  have hr96 := hrad 96 (by norm_num)
  have hslope := kernelSlope_nonneg (1 - θ)
  have hAmp : 0 ≤ paperAmplitude 8000 θ := by unfold paperAmplitude; positivity
  have hrot := BstLean.Part195.rotationConstant_nonneg 24
  unfold paperIdeal paperBias
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hscalar
  gcongr

end BstLean.BlueprintLow
