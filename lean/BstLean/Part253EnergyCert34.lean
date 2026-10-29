import BstLean.Part253EnergyUpper
import BstLean.Part253Retune

/-! Local upper computed-centre energy certificates. -/
namespace BstLean.Part253
open Real Set BstLean.Part130 BstLean.Part211 BstLean.Part206

theorem upperEnergyCell34 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 34) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 34 := by
  have hk1 : kappa q ≤ 0.608534005033 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 34 ≤ (0.499219099228 : ℝ)
      from by norm_num [noiseNode])) (s := (0.866475787871 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.610519618750 : ℝ) ≤ 0.685227917992 := by
    apply kappa_upper_rational (q := (0.610519618750 : ℝ)) (Q := (0.610519618750 : ℝ))
      (s := (0.792001133283 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.780348001208 : ℝ)) (R := (0.780914725462 : ℝ))
    (Q2 := (0.610519618750 : ℝ)) (T := (0.828254076779 : ℝ)) (B := retunedEnergy 34) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell35 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 35) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 35 := by
  have hk1 : kappa q ≤ 0.607733975741 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 35 ≤ (0.498019660970 : ℝ)
      from by norm_num [noiseNode])) (s := (0.867165738073 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.609718100007 : ℝ) ≤ 0.684657542999 := by
    apply kappa_upper_rational (q := (0.609718100007 : ℝ)) (Q := (0.609718100007 : ℝ))
      (s := (0.792618343545 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.779835222144 : ℝ)) (R := (0.780401946398 : ℝ))
    (Q2 := (0.609718100007 : ℝ)) (T := (0.827909290943 : ℝ)) (B := retunedEnergy 35) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell36 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 36) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 36 := by
  have hk1 : kappa q ≤ 0.606934489730 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 36 ≤ (0.496820222712 : ℝ)
      from by norm_num [noiseNode])) (s := (0.867853482049 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.608917125176 : ℝ) ≤ 0.684087827574 := by
    apply kappa_upper_rational (q := (0.608917125176 : ℝ)) (Q := (0.608917125176 : ℝ))
      (s := (0.793233846144 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.779322454242 : ℝ)) (R := (0.779889178496 : ℝ))
    (Q2 := (0.608917125176 : ℝ)) (T := (0.827564760410 : ℝ)) (B := retunedEnergy 36) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell37 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 37) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 37 := by
  have hk1 : kappa q ≤ 0.606135546404 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 37 ≤ (0.495620784454 : ℝ)
      from by norm_num [noiseNode])) (s := (0.868539025040 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.608116693657 : ℝ) ≤ 0.683518770498 := by
    apply kappa_upper_rational (q := (0.608116693657 : ℝ)) (Q := (0.608116693657 : ℝ))
      (s := (0.793847647157 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.778809697140 : ℝ)) (R := (0.779376421394 : ℝ))
    (Q2 := (0.608116693657 : ℝ)) (T := (0.827220484762 : ℝ)) (B := retunedEnergy 37) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell38 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 38) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 38 := by
  have hk1 : kappa q ≤ 0.605337145172 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 38 ≤ (0.494421346196 : ℝ)
      from by norm_num [noiseNode])) (s := (0.869222372254 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.607316804860 : ℝ) ≤ 0.682950370559 := by
    apply kappa_upper_rational (q := (0.607316804860 : ℝ)) (Q := (0.607316804860 : ℝ))
      (s := (0.794459752622 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.778296950481 : ℝ)) (R := (0.778863674735 : ℝ))
    (Q2 := (0.607316804860 : ℝ)) (T := (0.826876463585 : ℝ)) (B := retunedEnergy 38) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell39 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 39) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 39 := by
  have hk1 : kappa q ≤ 0.604539285445 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 39 ≤ (0.493221907938 : ℝ)
      from by norm_num [noiseNode])) (s := (0.869903528864 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.606517458193 : ℝ) ≤ 0.682382626545 := by
    apply kappa_upper_rational (q := (0.606517458193 : ℝ)) (Q := (0.606517458193 : ℝ))
      (s := (0.795070168544 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.777784213906 : ℝ)) (R := (0.778350938160 : ℝ))
    (Q2 := (0.606517458193 : ℝ)) (T := (0.826532696462 : ℝ)) (B := retunedEnergy 39) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

end BstLean.Part253
