import BstLean.Part253EnergyUpper
import BstLean.Part253Retune

/-! Local upper computed-centre energy certificates. -/
namespace BstLean.Part253
open Real Set BstLean.Part130 BstLean.Part211 BstLean.Part206

theorem upperEnergyCell16 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 16) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 16 := by
  have hk1 : kappa q ≤ 0.623028130623 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 16 ≤ (0.520808987872 : ℝ)
      from by norm_num [noiseNode])) (s := (0.853673238513 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.625040663252 : ℝ) ≤ 0.695608867965 := by
    apply kappa_upper_rational (q := (0.625040663252 : ℝ)) (Q := (0.625040663252 : ℝ))
      (s := (0.780592191405 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.789580349666 : ℝ)) (R := (0.790147073920 : ℝ))
    (Q2 := (0.625040663252 : ℝ)) (T := (0.834504365110 : ℝ)) (B := retunedEnergy 16) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell17 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 17) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 17 := by
  have hk1 : kappa q ≤ 0.622218216906 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 17 ≤ (0.519609549614 : ℝ)
      from by norm_num [noiseNode])) (s := (0.854403836573 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.624229248573 : ℝ) ≤ 0.695026407608 := by
    apply kappa_upper_rational (q := (0.624229248573 : ℝ)) (Q := (0.624229248573 : ℝ))
      (s := (0.781241220896 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.789067306927 : ℝ)) (R := (0.789634031181 : ℝ))
    (Q2 := (0.624229248573 : ℝ)) (T := (0.834154910463 : ℝ)) (B := retunedEnergy 17) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell18 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 18) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 18 := by
  have hk1 : kappa q ≤ 0.621408857723 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 18 ≤ (0.518410111356 : ℝ)
      from by norm_num [noiseNode])) (s := (0.855132128063 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.623418389078 : ℝ) ≤ 0.694444629473 := by
    apply kappa_upper_rational (q := (0.623418389078 : ℝ)) (Q := (0.623418389078 : ℝ))
      (s := (0.781888426926 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.788554282012 : ℝ)) (R := (0.789121006266 : ℝ))
    (Q2 := (0.623418389078 : ℝ)) (T := (0.833805718921 : ℝ)) (B := retunedEnergy 18) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell19 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 19) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 19 := by
  have hk1 : kappa q ≤ 0.620600052423 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 19 ≤ (0.517210673098 : ℝ)
      from by norm_num [noiseNode])) (s := (0.855858118869 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.622608084113 : ℝ) ≤ 0.693863532265 := by
    apply kappa_upper_rational (q := (0.622608084113 : ℝ)) (Q := (0.622608084113 : ℝ))
      (s := (0.782533816265 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.788041274540 : ℝ)) (R := (0.788607998794 : ℝ))
    (Q2 := (0.622608084113 : ℝ)) (T := (0.833456790039 : ℝ)) (B := retunedEnergy 19) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell20 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 20) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 20 := by
  have hk1 : kappa q ≤ 0.619791800357 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 20 ≤ (0.516011234840 : ℝ)
      from by norm_num [noiseNode])) (s := (0.856581814843 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.621798333029 : ℝ) ≤ 0.693283114694 := by
    apply kappa_upper_rational (q := (0.621798333029 : ℝ)) (Q := (0.621798333029 : ℝ))
      (s := (0.783177395641 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.787528284135 : ℝ)) (R := (0.788095008389 : ℝ))
    (Q2 := (0.621798333029 : ℝ)) (T := (0.833108123370 : ℝ)) (B := retunedEnergy 20) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell21 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 21) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 21 := by
  have hk1 : kappa q ≤ 0.618984100878 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 21 ≤ (0.514811796582 : ℝ)
      from by norm_num [noiseNode])) (s := (0.857303221795 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.620989135179 : ℝ) ≤ 0.692703375475 := by
    apply kappa_upper_rational (q := (0.620989135179 : ℝ)) (Q := (0.620989135179 : ℝ))
      (s := (0.783819171742 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.787015310419 : ℝ)) (R := (0.787582034673 : ℝ))
    (Q2 := (0.620989135179 : ℝ)) (T := (0.832759718472 : ℝ)) (B := retunedEnergy 21) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

end BstLean.Part253
