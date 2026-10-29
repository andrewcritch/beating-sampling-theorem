import BstLean.Part291Ideal
import BstLean.Part291Band
namespace BstLean.BlueprintLow
open Real Set BstLean.Part182 BstLean.Part215 BstLean.Part219
open scoped ENNReal

theorem directionIdealCell0 {θ e : ℝ} (hw : θ ∈ Icc (0.472 : ℝ) 0.479)
    (he : 0.665 ≤ e) : paperIdeal 8000 θ e ≤ 0.235 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 8000 θ ≤ 0.72672312 :=
    directionAmplitude8000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.48526447 := by
    apply BstLean.Part253.slope_upper (Q := (0.528 : ℝ)) (K := (0.62789549 : ℝ)) (s := (0.84924438 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith) <;> norm_num
  have h1 : radiusCoefficient 8000 1 θ ≤ 0.47911475 :=
    directionRadius8000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 8000 4 θ ≤ 0.47928698 :=
    directionRadius8000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 8000 24 θ ≤ 0.48043832 :=
    directionRadius8000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 8000 48 θ ≤ 0.48182725 :=
    directionRadius8000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 8000 96 θ ≤ 0.48462934 :=
    directionRadius8000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply directionIdeal8000_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.48043832 : ℝ) ≤ 0.69313659 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.47911475 : ℝ) / 8000) ≤ 0.00773883 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.479 : ℝ) ≤ 0.69209826 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.48526447 : ℝ) * 0.72672312 * 0.48182725 * 1.002934 / 0.815475 +
        (77 / 100) * 0.69313659 / 0.815475 *
          (0.00773883 + 0.72672312 * 6.7 * 0.48462934 * 1.005921 / 89.442719 +
            2 * ((0.479 + 0.69209826 * 0.47928698 * 1.000188) / 8000)) := by gcongr
    _ ≤ (0.235 : ℝ) := by norm_num

theorem directionIdealCell1 {θ e : ℝ} (hw : θ ∈ Icc (0.479 : ℝ) 0.486)
    (he : 0.665 ≤ e) : paperIdeal 8000 θ e ≤ 0.235 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 8000 θ ≤ 0.72189102 :=
    directionAmplitude8000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.48206207 := by
    apply BstLean.Part253.slope_upper (Q := (0.521 : ℝ)) (K := (0.62315717 : ℝ)) (s := (0.85355668 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith) <;> norm_num
  have h1 : radiusCoefficient 8000 1 θ ≤ 0.48611813 :=
    directionRadius8000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 8000 4 θ ≤ 0.48629543 :=
    directionRadius8000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 8000 24 θ ≤ 0.48748073 :=
    directionRadius8000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 8000 48 θ ≤ 0.48891074 :=
    directionRadius8000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 8000 96 θ ≤ 0.49179607 :=
    directionRadius8000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply directionIdeal8000_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.48748073 : ℝ) ≤ 0.69819821 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.48611813 : ℝ) / 8000) ≤ 0.00779518 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.486 : ℝ) ≤ 0.69713701 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.48206207 : ℝ) * 0.72189102 * 0.48891074 * 1.002934 / 0.815475 +
        (77 / 100) * 0.69819821 / 0.815475 *
          (0.00779518 + 0.72189102 * 6.7 * 0.49179607 * 1.005921 / 89.442719 +
            2 * ((0.486 + 0.69713701 * 0.48629543 * 1.000188) / 8000)) := by gcongr
    _ ≤ (0.235 : ℝ) := by norm_num

theorem directionIdealCell2 {θ e : ℝ} (hw : θ ∈ Icc (0.486 : ℝ) 0.493)
    (he : 0.665 ≤ e) : paperIdeal 8000 θ e ≤ 0.235 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 8000 θ ≤ 0.71702632 :=
    directionAmplitude8000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.47889171 := by
    apply BstLean.Part253.slope_upper (Q := (0.514 : ℝ)) (K := (0.61843776 : ℝ)) (s := (0.85779019 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith) <;> norm_num
  have h1 : radiusCoefficient 8000 1 θ ≤ 0.49312156 :=
    directionRadius8000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 8000 4 θ ≤ 0.49330400 :=
    directionRadius8000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 8000 24 θ ≤ 0.49452376 :=
    directionRadius8000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 8000 48 θ ≤ 0.49599545 :=
    directionRadius8000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 8000 96 θ ≤ 0.49896526 :=
    directionRadius8000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply directionIdeal8000_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.49452376 : ℝ) ≤ 0.70322384 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.49312156 : ℝ) / 8000) ≤ 0.00785113 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.493 : ℝ) ≤ 0.70213959 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47889171 : ℝ) * 0.71702632 * 0.49599545 * 1.002934 / 0.815475 +
        (77 / 100) * 0.70322384 / 0.815475 *
          (0.00785113 + 0.71702632 * 6.7 * 0.49896526 * 1.005921 / 89.442719 +
            2 * ((0.493 + 0.70213959 * 0.49330400 * 1.000188) / 8000)) := by gcongr
    _ ≤ (0.235 : ℝ) := by norm_num

theorem directionIdealCell3 {θ e : ℝ} (hw : θ ∈ Icc (0.493 : ℝ) 0.500)
    (he : 0.665 ≤ e) : paperIdeal 8000 θ e ≤ 0.235 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 8000 θ ≤ 0.71212835 :=
    directionAmplitude8000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.47575265 := by
    apply BstLean.Part253.slope_upper (Q := (0.507 : ℝ)) (K := (0.61373713 : ℝ)) (s := (0.86194606 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith) <;> norm_num
  have h1 : radiusCoefficient 8000 1 θ ≤ 0.50012504 :=
    directionRadius8000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 8000 4 θ ≤ 0.50031270 :=
    directionRadius8000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 8000 24 θ ≤ 0.50156740 :=
    directionRadius8000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 8000 48 θ ≤ 0.50308138 :=
    directionRadius8000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 8000 96 θ ≤ 0.50613692 :=
    directionRadius8000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply directionIdeal8000_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.50156740 : ℝ) ≤ 0.70821424 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.50012504 : ℝ) / 8000) ≤ 0.00790669 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.500 : ℝ) ≤ 0.70710679 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47575265 : ℝ) * 0.71212835 * 0.50308138 * 1.002934 / 0.815475 +
        (77 / 100) * 0.70821424 / 0.815475 *
          (0.00790669 + 0.71212835 * 6.7 * 0.50613692 * 1.005921 / 89.442719 +
            2 * ((0.500 + 0.70710679 * 0.50031270 * 1.000188) / 8000)) := by gcongr
    _ ≤ (0.235 : ℝ) := by norm_num

theorem directionIdealCell4 {θ e : ℝ} (hw : θ ∈ Icc (0.500 : ℝ) 0.507)
    (he : 0.665 ≤ e) : paperIdeal 8000 θ e ≤ 0.235 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 8000 θ ≤ 0.70719643 :=
    directionAmplitude8000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.47264416 := by
    apply BstLean.Part253.slope_upper (Q := (0.500 : ℝ)) (K := (0.60905517 : ℝ)) (s := (0.86602541 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith) <;> norm_num
  have h1 : radiusCoefficient 8000 1 θ ≤ 0.50712856 :=
    directionRadius8000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 8000 4 θ ≤ 0.50732152 :=
    directionRadius8000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 8000 24 θ ≤ 0.50861167 :=
    directionRadius8000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 8000 48 θ ≤ 0.51016853 :=
    directionRadius8000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 8000 96 θ ≤ 0.51331104 :=
    directionRadius8000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply directionIdeal8000_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.50861167 : ℝ) ≤ 0.71317016 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.50712856 : ℝ) / 8000) ≤ 0.00796186 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.507 : ℝ) ≤ 0.71203933 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.47264416 : ℝ) * 0.70719643 * 0.51016853 * 1.002934 / 0.815475 +
        (77 / 100) * 0.71317016 / 0.815475 *
          (0.00796186 + 0.70719643 * 6.7 * 0.51331104 * 1.005921 / 89.442719 +
            2 * ((0.507 + 0.71203933 * 0.50732152 * 1.000188) / 8000)) := by gcongr
    _ ≤ (0.235 : ℝ) := by norm_num

theorem directionIdealCell5 {θ e : ℝ} (hw : θ ∈ Icc (0.507 : ℝ) 0.514)
    (he : 0.665 ≤ e) : paperIdeal 8000 θ e ≤ 0.235 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 8000 θ ≤ 0.70222983 :=
    directionAmplitude8000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.46956553 := by
    apply BstLean.Part253.slope_upper (Q := (0.493 : ℝ)) (K := (0.60439174 : ℝ)) (s := (0.87002931 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith) <;> norm_num
  have h1 : radiusCoefficient 8000 1 θ ≤ 0.51413214 :=
    directionRadius8000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 8000 4 θ ≤ 0.51433046 :=
    directionRadius8000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 8000 24 θ ≤ 0.51565655 :=
    directionRadius8000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 8000 48 θ ≤ 0.51725691 :=
    directionRadius8000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 8000 96 θ ≤ 0.52048762 :=
    directionRadius8000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply directionIdeal8000_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.51565655 : ℝ) ≤ 0.71809230 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.51413214 : ℝ) / 8000) ≤ 0.00801665 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.514 : ℝ) ≤ 0.71693794 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.46956553 : ℝ) * 0.70222983 * 0.51725691 * 1.002934 / 0.815475 +
        (77 / 100) * 0.71809230 / 0.815475 *
          (0.00801665 + 0.70222983 * 6.7 * 0.52048762 * 1.005921 / 89.442719 +
            2 * ((0.514 + 0.71693794 * 0.51433046 * 1.000188) / 8000)) := by gcongr
    _ ≤ (0.235 : ℝ) := by norm_num

theorem directionIdealCell6 {θ e : ℝ} (hw : θ ∈ Icc (0.514 : ℝ) 0.521)
    (he : 0.665 ≤ e) : paperIdeal 8000 θ e ≤ 0.235 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 8000 θ ≤ 0.69722783 :=
    directionAmplitude8000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.46651609 := by
    apply BstLean.Part253.slope_upper (Q := (0.486 : ℝ)) (K := (0.59974673 : ℝ)) (s := (0.87395881 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith) <;> norm_num
  have h1 : radiusCoefficient 8000 1 θ ≤ 0.52113576 :=
    directionRadius8000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 8000 4 θ ≤ 0.52133953 :=
    directionRadius8000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 8000 24 θ ≤ 0.52270205 :=
    directionRadius8000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 8000 48 θ ≤ 0.52434652 :=
    directionRadius8000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 8000 96 θ ≤ 0.52766668 :=
    directionRadius8000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply directionIdeal8000_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.52270205 : ℝ) ≤ 0.72298137 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.52113576 : ℝ) / 8000) ≤ 0.00807106 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.521 : ℝ) ≤ 0.72180330 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.46651609 : ℝ) * 0.69722783 * 0.52434652 * 1.002934 / 0.815475 +
        (77 / 100) * 0.72298137 / 0.815475 *
          (0.00807106 + 0.69722783 * 6.7 * 0.52766668 * 1.005921 / 89.442719 +
            2 * ((0.521 + 0.72180330 * 0.52133953 * 1.000188) / 8000)) := by gcongr
    _ ≤ (0.235 : ℝ) := by norm_num

theorem directionIdealCell7 {θ e : ℝ} (hw : θ ∈ Icc (0.521 : ℝ) 0.528)
    (he : 0.665 ≤ e) : paperIdeal 8000 θ e ≤ 0.235 := by
  have hθ : 0 ≤ θ := le_trans (by norm_num) hw.1
  have hAmp : paperAmplitude 8000 θ ≤ 0.69218964 :=
    directionAmplitude8000 hw.1 hw.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hSlope : BstLean.Part219.kernelSlope (1 - θ) ≤ 0.46349519 := by
    apply BstLean.Part253.slope_upper (Q := (0.479 : ℝ)) (K := (0.59512003 : ℝ)) (s := (0.87781491 : ℝ))
      (by have := hw.2; linarith) (by have := hw.1; linarith) <;> norm_num
  have h1 : radiusCoefficient 8000 1 θ ≤ 0.52813943 :=
    directionRadius8000 1 hθ hw.2 (by norm_num) (by norm_num)
  have h4 : radiusCoefficient 8000 4 θ ≤ 0.52834872 :=
    directionRadius8000 4 hθ hw.2 (by norm_num) (by norm_num)
  have h24 : radiusCoefficient 8000 24 θ ≤ 0.52974817 :=
    directionRadius8000 24 hθ hw.2 (by norm_num) (by norm_num)
  have h48 : radiusCoefficient 8000 48 θ ≤ 0.53143734 :=
    directionRadius8000 48 hθ hw.2 (by norm_num) (by norm_num)
  have h96 : radiusCoefficient 8000 96 θ ≤ 0.53484820 :=
    directionRadius8000 96 hθ hw.2 (by norm_num) (by norm_num)
  apply directionIdeal8000_from_bounds hθ he hw.2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hAmp hSlope h1 h4 h24 h48 h96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs24 : √(0.52974817 : ℝ) ≤ 0.72783802 := sqrt_le_iff.mpr (by norm_num)
  have hs1 : √((0.52813943 : ℝ) / 8000) ≤ 0.00812512 := sqrt_le_iff.mpr (by norm_num)
  have hsT : √(0.528 : ℝ) ≤ 0.72663609 := sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ (0.46349519 : ℝ) * 0.69218964 * 0.53143734 * 1.002934 / 0.815475 +
        (77 / 100) * 0.72783802 / 0.815475 *
          (0.00812512 + 0.69218964 * 6.7 * 0.53484820 * 1.005921 / 89.442719 +
            2 * ((0.528 + 0.72663609 * 0.52834872 * 1.000188) / 8000)) := by gcongr
    _ ≤ (0.235 : ℝ) := by norm_num

theorem directionIdealBandEndpoint {θ e : ℝ}
    (hw : θ ∈ Icc (0.472 : ℝ) 0.528) (he : 0.665 ≤ e) : paperIdeal 8000 θ e ≤ 0.235 := by
  by_cases h0 : θ ≤ 0.479
  · exact directionIdealCell0 ⟨by linarith [hw.1], h0⟩ he
  by_cases h1 : θ ≤ 0.486
  · exact directionIdealCell1 ⟨by linarith [hw.1], h1⟩ he
  by_cases h2 : θ ≤ 0.493
  · exact directionIdealCell2 ⟨by linarith [hw.1], h2⟩ he
  by_cases h3 : θ ≤ 0.500
  · exact directionIdealCell3 ⟨by linarith [hw.1], h3⟩ he
  by_cases h4 : θ ≤ 0.507
  · exact directionIdealCell4 ⟨by linarith [hw.1], h4⟩ he
  by_cases h5 : θ ≤ 0.514
  · exact directionIdealCell5 ⟨by linarith [hw.1], h5⟩ he
  by_cases h6 : θ ≤ 0.521
  · exact directionIdealCell6 ⟨by linarith [hw.1], h6⟩ he
  exact directionIdealCell7 ⟨by linarith, hw.2⟩ he

/-- The directional source bound permits full centre error .14. -/
theorem agentDirectionBand {n : ℕ} (hn : 8000 ≤ n)
    (c : Fin n → ℝ) (τ e xi eta : ℝ) (δ : ℝ≥0∞)
    (hw : BstLean.Part150.thetaC c τ ∈ Icc (0.472 : ℝ) 0.528)
    (he : 0.665 ≤ e) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.14)
    (hop : operatorAllowance c τ eta δ ^ 2 ≤ 1.269) :
    paperDirectionBudget c τ e xi eta δ ≤ agentDirectionCap := by
  have hroot : (0.88 : ℝ) ≤ (7 / 25000 : ℝ) ^ (1 / 64 : ℝ) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (64 : ℕ) ≠ 0) (by positivity)
    have hh := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 7 / 25000)
      (by norm_num : (64 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hh
    rw [hh]
    norm_num
  have h := BstLean.Part277.direction_budget_leP (n0 := 8000) (by norm_num) hn c τ e xi eta δ
    (θlo := 0.472) (θhi := 0.528) (e0 := 0.665) (xi0 := 0.14) (MP := 1.269)
    (I0 := 0.235) (ε0 := 0.087) (Rc := 0.528908) (sR := 0.892) (ρ0 := 0.88)
    (by norm_num) hw (by norm_num) (by norm_num) he hxi hxi1 hop (by norm_num)
    (fun θ hθ e' he' => directionIdealBandEndpoint hθ he')
    (fun θ hθ => directionRadius8000 12 (le_trans (by norm_num) hθ.1) hθ.2
      (by norm_num) (by norm_num))
    directionError8000 (by norm_num) (by norm_num) (by norm_num) hroot
  refine h.trans ?_
  have hs : √((1.269 : ℝ) * 0.14 / ((8000 : ℕ) * 0.665)) ≤ 0.00578 :=
    sqrt_le_iff.mpr (by norm_num)
  calc
    _ ≤ ((0.235 : ℝ) + 0.087 * 0.892 / 0.88 + 0.00578) ^ 2 := by gcongr
    _ ≤ agentDirectionCap := by norm_num [agentDirectionCap]

end BstLean.BlueprintLow
