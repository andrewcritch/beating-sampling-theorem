import BstLean.Part253Ideal

/-! The interval certificates bound the deterministic ideal term. -/
namespace BstLean.Part253
open Real Set BstLean.Part219 BstLean.Part215

theorem idealCell0 {θ e : ℝ} (hw : θ ∈ Icc (0.47199 : ℝ) 0.4744)
    (he : 0.665 ≤ e) : paperIdeal 12225 θ e ≤ 0.230 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12225 θ ≤ 0.72669937 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.48526907 := by
    apply slope_upper (Q := (0.52801 : ℝ)) (K := (0.62790227 : ℝ)) (s := (0.84923816 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12225 1 θ ≤ 0.47447365 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12225 4 θ ≤ 0.47458417 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12225 24 θ ≤ 0.47532227 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12225 48 θ ≤ 0.47621102 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12225 96 θ ≤ 0.47799853 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.47532227 : ℝ) ≤ 0.68943620 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.47447365 : ℝ) / 12225) ≤ 0.00622991 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4744 : ℝ) ≤ 0.68876702 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.48526907 : ℝ) * 0.72669937 * 0.47621102 * 1.001921 / 0.815475 +
        (77 / 100) * 0.68943620 / 0.815475 *
          (0.00622991 + 0.72669937 * 6.7 * 0.47799853 * 1.003879 / 110.566721 +
            2 * ((0.4744 + 0.68876702 * 0.47458417 * 1.000123) / 12225)) := by gcongr
    _ ≤ (0.230 : ℝ) := by norm_num

theorem idealCell1 {θ e : ℝ} (hw : θ ∈ Icc (0.4744 : ℝ) 0.4816)
    (he : 0.665 ≤ e) : paperIdeal 12225 θ e ≤ 0.230 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12225 θ ≤ 0.72503989 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.48416285 := by
    apply slope_upper (Q := (0.5256 : ℝ)) (K := (0.62626878 : ℝ)) (s := (0.85073183 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12225 1 θ ≤ 0.48167591 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12225 4 θ ≤ 0.48178980 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12225 24 θ ≤ 0.48255050 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12225 48 θ ≤ 0.48346651 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12225 96 θ ≤ 0.48530901 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.48255050 : ℝ) ≤ 0.69465855 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.48167591 : ℝ) / 12225) ≤ 0.00627702 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4816 : ℝ) ≤ 0.69397407 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.48416285 : ℝ) * 0.72503989 * 0.48346651 * 1.001921 / 0.815475 +
        (77 / 100) * 0.69465855 / 0.815475 *
          (0.00627702 + 0.72503989 * 6.7 * 0.48530901 * 1.003879 / 110.566721 +
            2 * ((0.4816 + 0.69397407 * 0.48178980 * 1.000123) / 12225)) := by gcongr
    _ ≤ (0.230 : ℝ) := by norm_num

theorem idealCell2 {θ e : ℝ} (hw : θ ∈ Icc (0.4816 : ℝ) 0.4888)
    (he : 0.665 ≤ e) : paperIdeal 12225 θ e ≤ 0.230 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12225 θ ≤ 0.72005759 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.48088081 := by
    apply slope_upper (Q := (0.5184 : ℝ)) (K := (0.62140204 : ℝ)) (s := (0.85513826 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12225 1 θ ≤ 0.48887819 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12225 4 θ ≤ 0.48899552 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12225 24 θ ≤ 0.48977916 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12225 48 θ ≤ 0.49072285 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12225 96 θ ≤ 0.49262118 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.48977916 : ℝ) ≤ 0.69984224 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.48887819 : ℝ) / 12225) ≤ 0.00632377 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.4888 : ℝ) ≤ 0.69914234 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.48088081 : ℝ) * 0.72005759 * 0.49072285 * 1.001921 / 0.815475 +
        (77 / 100) * 0.69984224 / 0.815475 *
          (0.00632377 + 0.72005759 * 6.7 * 0.49262118 * 1.003879 / 110.566721 +
            2 * ((0.4888 + 0.69914234 * 0.48899552 * 1.000123) / 12225)) := by gcongr
    _ ≤ (0.230 : ℝ) := by norm_num

theorem idealCell3 {θ e : ℝ} (hw : θ ∈ Icc (0.4888 : ℝ) 0.496)
    (he : 0.665 ≤ e) : paperIdeal 12225 θ e ≤ 0.230 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12225 θ ≤ 0.71504055 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.47763237 := by
    apply slope_upper (Q := (0.5112 : ℝ)) (K := (0.61655526 : ℝ)) (s := (0.85946179 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12225 1 θ ≤ 0.49608051 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12225 4 θ ≤ 0.49620133 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12225 24 θ ≤ 0.49700825 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12225 48 θ ≤ 0.49798003 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12225 96 θ ≤ 0.49993504 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.49700825 : ℝ) ≤ 0.70498813 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.49608051 : ℝ) / 12225) ≤ 0.00637018 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.496 : ℝ) ≤ 0.70427268 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47763237 : ℝ) * 0.71504055 * 0.49798003 * 1.001921 / 0.815475 +
        (77 / 100) * 0.70498813 / 0.815475 *
          (0.00637018 + 0.71504055 * 6.7 * 0.49993504 * 1.003879 / 110.566721 +
            2 * ((0.496 + 0.70427268 * 0.49620133 * 1.000123) / 12225)) := by gcongr
    _ ≤ (0.230 : ℝ) := by norm_num

end BstLean.Part253
