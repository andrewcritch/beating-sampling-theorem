import BstLean.Part253Ideal

/-! The interval certificates bound the deterministic ideal term. -/
namespace BstLean.Part253
open Real Set BstLean.Part219 BstLean.Part215

theorem idealCell4 {θ e : ℝ} (hw : θ ∈ Icc (0.496 : ℝ) 0.5032)
    (he : 0.665 ≤ e) : paperIdeal 12225 θ e ≤ 0.230 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12225 θ ≤ 0.70998803 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.47441674 := by
    apply slope_upper (Q := (0.504 : ℝ)) (K := (0.61172830 : ℝ)) (s := (0.86370366 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12225 1 θ ≤ 0.50328287 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12225 4 θ ≤ 0.50340722 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12225 24 θ ≤ 0.50423777 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12225 48 θ ≤ 0.50523805 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12225 96 θ ≤ 0.50725057 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.50423777 : ℝ) ≤ 0.71009702 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.50328287 : ℝ) / 12225) ≤ 0.00641626 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5032 : ℝ) ≤ 0.70936592 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47441674 : ℝ) * 0.70998803 * 0.50523805 * 1.001921 / 0.815475 +
        (77 / 100) * 0.71009702 / 0.815475 *
          (0.00641626 + 0.70998803 * 6.7 * 0.50725057 * 1.003879 / 110.566721 +
            2 * ((0.5032 + 0.70936592 * 0.50340722 * 1.000123) / 12225)) := by gcongr
    _ ≤ (0.230 : ℝ) := by norm_num

theorem idealCell5 {θ e : ℝ} (hw : θ ∈ Icc (0.5032 : ℝ) 0.5104)
    (he : 0.665 ≤ e) : paperIdeal 12225 θ e ≤ 0.230 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12225 θ ≤ 0.70489927 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.47123312 := by
    apply slope_upper (Q := (0.4968 : ℝ)) (K := (0.60692102 : ℝ)) (s := (0.86786506 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12225 1 θ ≤ 0.51048526 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12225 4 θ ≤ 0.51061319 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12225 24 θ ≤ 0.51146771 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12225 48 θ ≤ 0.51249691 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12225 96 θ ≤ 0.51456780 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.51146771 : ℝ) ≤ 0.71516971 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.51048526 : ℝ) / 12225) ≤ 0.00646201 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5104 : ℝ) ≤ 0.71442285 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47123312 : ℝ) * 0.70489927 * 0.51249691 * 1.001921 / 0.815475 +
        (77 / 100) * 0.71516971 / 0.815475 *
          (0.00646201 + 0.70489927 * 6.7 * 0.51456780 * 1.003879 / 110.566721 +
            2 * ((0.5104 + 0.71442285 * 0.51061319 * 1.000123) / 12225)) := by gcongr
    _ ≤ (0.230 : ℝ) := by norm_num

theorem idealCell6 {θ e : ℝ} (hw : θ ∈ Icc (0.5104 : ℝ) 0.5176)
    (he : 0.665 ≤ e) : paperIdeal 12225 θ e ≤ 0.230 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12225 θ ≤ 0.69977349 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.46808077 := by
    apply slope_upper (Q := (0.4896 : ℝ)) (K := (0.60213330 : ℝ)) (s := (0.87194716 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12225 1 θ ≤ 0.51768768 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12225 4 θ ≤ 0.51781925 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12225 24 θ ≤ 0.51869808 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12225 48 θ ≤ 0.51975661 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12225 96 θ ≤ 0.52188671 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.51869808 : ℝ) ≤ 0.72020698 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.51768768 : ℝ) / 12225) ≤ 0.00650743 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.5176 : ℝ) ≤ 0.71944423 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.46808077 : ℝ) * 0.69977349 * 0.51975661 * 1.001921 / 0.815475 +
        (77 / 100) * 0.72020698 / 0.815475 *
          (0.00650743 + 0.69977349 * 6.7 * 0.52188671 * 1.003879 / 110.566721 +
            2 * ((0.5176 + 0.71944423 * 0.51781925 * 1.000123) / 12225)) := by gcongr
    _ ≤ (0.230 : ℝ) := by norm_num

theorem idealCell7 {θ e : ℝ} (hw : θ ∈ Icc (0.5176 : ℝ) 0.52358)
    (he : 0.665 ≤ e) : paperIdeal 12225 θ e ≤ 0.230 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 12225 θ ≤ 0.69460972 :=
    amplitude_upper hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : kernelSlope (1 - θ) ≤ 0.46495896 := by
    apply slope_upper (Q := (0.4824 : ℝ)) (K := (0.59736500 : ℝ)) (s := (0.87595105 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith)
      <;> norm_num
  have h1 : radiusCoefficient 12225 1 θ ≤ 0.52366972 :=
    radius_upper 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 12225 4 θ ≤ 0.52380434 :=
    radius_upper 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 12225 24 θ ≤ 0.52470362 :=
    radius_upper 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 12225 48 θ ≤ 0.52578684 :=
    radius_upper 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 12225 96 θ ≤ 0.52796675 :=
    radius_upper 96 hθ hw.2 (by norm_num) (by norm_num)
  apply ideal_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.52470362 : ℝ) ≤ 0.72436429 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.52366972 : ℝ) / 12225) ≤ 0.00654492 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.52358 : ℝ) ≤ 0.72358829 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.46495896 : ℝ) * 0.69460972 * 0.52578684 * 1.001921 / 0.815475 +
        (77 / 100) * 0.72436429 / 0.815475 *
          (0.00654492 + 0.69460972 * 6.7 * 0.52796675 * 1.003879 / 110.566721 +
            2 * ((0.52358 + 0.72358829 * 0.52380434 * 1.000123) / 12225)) := by gcongr
    _ ≤ (0.230 : ℝ) := by norm_num

end BstLean.Part253
