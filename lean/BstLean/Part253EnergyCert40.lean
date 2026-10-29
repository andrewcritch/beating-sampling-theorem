import BstLean.Part253EnergyUpper
import BstLean.Part253Retune

/-! Local upper computed-centre energy certificates. -/
namespace BstLean.Part253
open Real Set BstLean.Part130 BstLean.Part211 BstLean.Part206

theorem upperEnergyCell40 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 40) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 40 := by
  have hk1 : kappa q ≤ 0.603741966637 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 40 ≤ (0.492022469680 : ℝ)
      from by norm_num [noiseNode])) (s := (0.870582500014 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.605718653069 : ℝ) ≤ 0.681815537253 := by
    apply kappa_upper_rational (q := (0.605718653069 : ℝ)) (Q := (0.605718653069 : ℝ))
      (s := (0.795678900892 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.777271487058 : ℝ)) (R := (0.777838211312 : ℝ))
    (Q2 := (0.605718653069 : ℝ)) (T := (0.826189182980 : ℝ)) (B := retunedEnergy 40) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell41 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 41) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 41 := by
  have hk1 : kappa q ≤ 0.602945188166 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 41 ≤ (0.490823031422 : ℝ)
      from by norm_num [noiseNode])) (s := (0.871259290812 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.604920388907 : ℝ) ≤ 0.681249101484 := by
    apply kappa_upper_rational (q := (0.604920388907 : ℝ)) (Q := (0.604920388907 : ℝ))
      (s := (0.796285955600 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.776758769582 : ℝ)) (R := (0.777325493836 : ℝ))
    (Q2 := (0.604920388907 : ℝ)) (T := (0.825845922731 : ℝ)) (B := retunedEnergy 41) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell42 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 42) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 42 := by
  have hk1 : kappa q ≤ 0.602148949452 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 42 ≤ (0.489623593164 : ℝ)
      from by norm_num [noiseNode])) (s := (0.871933906336 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.604122665122 : ℝ) ≤ 0.680683318038 := by
    apply kappa_upper_rational (q := (0.604122665122 : ℝ)) (Q := (0.604122665122 : ℝ))
      (s := (0.796891338569 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.776246061122 : ℝ)) (R := (0.776812785376 : ℝ))
    (Q2 := (0.604122665122 : ℝ)) (T := (0.825502915301 : ℝ)) (B := retunedEnergy 42) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell43 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 43) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 43 := by
  have hk1 : kappa q ≤ 0.601353249920 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 43 ≤ (0.488424154906 : ℝ)
      from by norm_num [noiseNode])) (s := (0.872606351630 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.603325481143 : ℝ) ≤ 0.680118185727 := by
    apply kappa_upper_rational (q := (0.603325481143 : ℝ)) (Q := (0.603325481143 : ℝ))
      (s := (0.797495055661 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.775733361327 : ℝ)) (R := (0.776300085581 : ℝ))
    (Q2 := (0.603325481143 : ℝ)) (T := (0.825160160287 : ℝ)) (B := retunedEnergy 43) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell44 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 44) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 44 := by
  have hk1 : kappa q ≤ 0.600558088998 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 44 ≤ (0.487224716648 : ℝ)
      from by norm_num [noiseNode])) (s := (0.873276631709 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.602528836393 : ℝ) ≤ 0.679553703363 := by
    apply kappa_upper_rational (q := (0.602528836393 : ℝ)) (Q := (0.602528836393 : ℝ))
      (s := (0.798097112710 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.775220669844 : ℝ)) (R := (0.775787394098 : ℝ))
    (Q2 := (0.602528836393 : ℝ)) (T := (0.824817657280 : ℝ)) (B := retunedEnergy 44) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell45 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 45) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 45 := by
  have hk1 : kappa q ≤ 0.599763466114 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 45 ≤ (0.486025278390 : ℝ)
      from by norm_num [noiseNode])) (s := (0.873944751553 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.601732730301 : ℝ) ≤ 0.678989869762 := by
    apply kappa_upper_rational (q := (0.601732730301 : ℝ)) (Q := (0.601732730301 : ℝ))
      (s := (0.798697515512 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.774707986321 : ℝ)) (R := (0.775274710575 : ℝ))
    (Q2 := (0.601732730301 : ℝ)) (T := (0.824475405878 : ℝ)) (B := retunedEnergy 45) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

end BstLean.Part253
