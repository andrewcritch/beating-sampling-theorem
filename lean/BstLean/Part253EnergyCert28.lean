import BstLean.Part253EnergyUpper
import BstLean.Part253Retune

/-! Local upper computed-centre energy certificates. -/
namespace BstLean.Part253
open Real Set BstLean.Part130 BstLean.Part211 BstLean.Part206

theorem upperEnergyCell28 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 28) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 28 := by
  have hk1 : kappa q ≤ 0.613345623395 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 28 ≤ (0.506415728776 : ℝ)
      from by norm_num [noiseNode])) (s := (0.862289458157 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.615340187080 : ℝ) ≤ 0.688664087600 := by
    apply kappa_upper_rational (q := (0.615340187080 : ℝ)) (Q := (0.615340187080 : ℝ))
      (s := (0.788261666051 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.783424930259 : ℝ)) (R := (0.783991654513 : ℝ))
    (Q2 := (0.615340187080 : ℝ)) (T := (0.830328176789 : ℝ)) (B := retunedEnergy 28) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell29 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 29) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 29 := by
  have hk1 : kappa q ≤ 0.612542321746 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 29 ≤ (0.505216290518 : ℝ)
      from by norm_num [noiseNode])) (s := (0.862992757673 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.614535392183 : ℝ) ≤ 0.688089729387 := by
    apply kappa_upper_rational (q := (0.614535392183 : ℝ)) (Q := (0.614535392183 : ℝ))
      (s := (0.788889251895 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.782912076610 : ℝ)) (R := (0.783478800864 : ℝ))
    (Q2 := (0.614535392183 : ℝ)) (T := (0.829981850260 : ℝ)) (B := retunedEnergy 29) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell30 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 30) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 30 := by
  have hk1 : kappa q ≤ 0.611739567016 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 30 ≤ (0.504016852260 : ℝ)
      from by norm_num [noiseNode])) (s := (0.863693818803 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.613731144843 : ℝ) ≤ 0.687516038141 := by
    apply kappa_upper_rational (q := (0.613731144843 : ℝ)) (Q := (0.613731144843 : ℝ))
      (s := (0.789515092858 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.782399236306 : ℝ)) (R := (0.782965960560 : ℝ))
    (Q2 := (0.613731144843 : ℝ)) (T := (0.829635781579 : ℝ)) (B := retunedEnergy 30) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell31 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 31) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 31 := by
  have hk1 : kappa q ≤ 0.610937358588 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 31 ≤ (0.502817414002 : ℝ)
      from by norm_num [noiseNode])) (s := (0.864392646994 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.612927444439 : ℝ) ≤ 0.686943012616 := by
    apply kappa_upper_rational (q := (0.612927444439 : ℝ)) (Q := (0.612927444439 : ℝ))
      (s := (0.790139195240 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.781886408978 : ℝ)) (R := (0.782453133232 : ℝ))
    (Q2 := (0.612927444439 : ℝ)) (T := (0.829289970315 : ℝ)) (B := retunedEnergy 31) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell32 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 32) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 32 := by
  have hk1 : kappa q ≤ 0.610135695853 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 32 ≤ (0.501617975744 : ℝ)
      from by norm_num [noiseNode])) (s := (0.865089247657 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.612124290359 : ℝ) ≤ 0.686370651570 := by
    apply kappa_upper_rational (q := (0.612124290359 : ℝ)) (Q := (0.612124290359 : ℝ))
      (s := (0.790761565298 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.781373594261 : ℝ)) (R := (0.781940318515 : ℝ))
    (Q2 := (0.612124290359 : ℝ)) (T := (0.828944416043 : ℝ)) (B := retunedEnergy 32) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell33 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 33) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 33 := by
  have hk1 : kappa q ≤ 0.609334578203 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 33 ≤ (0.500418537486 : ℝ)
      from by norm_num [noiseNode])) (s := (0.865783626168 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.611321681998 : ℝ) ≤ 0.685798953773 := by
    apply kappa_upper_rational (q := (0.611321681998 : ℝ)) (Q := (0.611321681998 : ℝ))
      (s := (0.791382209252 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.780860791792 : ℝ)) (R := (0.781427516046 : ℝ))
    (Q2 := (0.611321681998 : ℝ)) (T := (0.828599118339 : ℝ)) (B := retunedEnergy 33) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

end BstLean.Part253
