import BstLean.Part253EnergyUpper
import BstLean.Part253Retune

/-! Local upper computed-centre energy certificates. -/
namespace BstLean.Part253
open Real Set BstLean.Part130 BstLean.Part211 BstLean.Part206

theorem upperEnergyCell46 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 46) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 46 := by
  have hk1 : kappa q ≤ 0.598969380702 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 46 ≤ (0.484825840132 : ℝ)
      from by norm_num [noiseNode])) (s := (0.874610716114 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.600937162300 : ℝ) ≤ 0.678426683745 := by
    apply kappa_upper_rational (q := (0.600937162300 : ℝ)) (Q := (0.600937162300 : ℝ))
      (s := (0.799296269832 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.774195310408 : ℝ)) (R := (0.774762034662 : ℝ))
    (Q2 := (0.600937162300 : ℝ)) (T := (0.824133405676 : ℝ)) (B := retunedEnergy 46) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell47 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 47) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 47 := by
  have hk1 : kappa q ≤ 0.598175832200 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 47 ≤ (0.483626401874 : ℝ)
      from by norm_num [noiseNode])) (s := (0.875274530311 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.600142131826 : ℝ) ≤ 0.677864144139 := by
    apply kappa_upper_rational (q := (0.600142131826 : ℝ)) (Q := (0.600142131826 : ℝ))
      (s := (0.799893381400 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.773682641757 : ℝ)) (R := (0.774249366011 : ℝ))
    (Q2 := (0.600142131826 : ℝ)) (T := (0.823791656276 : ℝ)) (B := retunedEnergy 47) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell48 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 48) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 48 := by
  have hk1 : kappa q ≤ 0.597382820046 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 48 ≤ (0.482426963616 : ℝ)
      from by norm_num [noiseNode])) (s := (0.875936199033 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.599347638315 : ℝ) ≤ 0.677302249772 := by
    apply kappa_upper_rational (q := (0.599347638315 : ℝ)) (Q := (0.599347638315 : ℝ))
      (s := (0.800488855917 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.773169980018 : ℝ)) (R := (0.773736704272 : ℝ))
    (Q2 := (0.599347638315 : ℝ)) (T := (0.823450157276 : ℝ)) (B := retunedEnergy 48) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell49 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 49) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 49 := by
  have hk1 : kappa q ≤ 0.596590343685 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 49 ≤ (0.481227525358 : ℝ)
      from by norm_num [noiseNode])) (s := (0.876595727139 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.598553681214 : ℝ) ≤ 0.676740999482 := by
    apply kappa_upper_rational (q := (0.598553681214 : ℝ)) (Q := (0.598553681214 : ℝ))
      (s := (0.801082699043 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.772657324848 : ℝ)) (R := (0.773224049102 : ℝ))
    (Q2 := (0.598553681214 : ℝ)) (T := (0.823108908282 : ℝ)) (B := retunedEnergy 49) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell50 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 50) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 50 := by
  have hk1 : kappa q ≤ 0.595798402560 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 50 ≤ (0.480028087100 : ℝ)
      from by norm_num [noiseNode])) (s := (0.877253119456 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.597760259962 : ℝ) ≤ 0.676180392104 := by
    apply kappa_upper_rational (q := (0.597760259962 : ℝ)) (Q := (0.597760259962 : ℝ))
      (s := (0.801674916416 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.772144675897 : ℝ)) (R := (0.772711400151 : ℝ))
    (Q2 := (0.597760259962 : ℝ)) (T := (0.822767908896 : ℝ)) (B := retunedEnergy 50) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell51 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 51) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 51 := by
  have hk1 : kappa q ≤ 0.595006996122 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 51 ≤ (0.478828648842 : ℝ)
      from by norm_num [noiseNode])) (s := (0.877908380783 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.596967374010 : ℝ) ≤ 0.675620426482 := by
    apply kappa_upper_rational (q := (0.596967374010 : ℝ)) (Q := (0.596967374010 : ℝ))
      (s := (0.802265513635 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.771632032822 : ℝ)) (R := (0.772198757076 : ℝ))
    (Q2 := (0.596967374010 : ℝ)) (T := (0.822427158726 : ℝ)) (B := retunedEnergy 51) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

end BstLean.Part253
