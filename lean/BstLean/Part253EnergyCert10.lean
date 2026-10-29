import BstLean.Part253EnergyUpper
import BstLean.Part253Retune

/-! Local upper computed-centre energy certificates. -/
namespace BstLean.Part253
open Real Set BstLean.Part130 BstLean.Part211 BstLean.Part206

theorem upperEnergyCell10 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 10) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 10 := by
  have hk1 : kappa q ≤ 0.627899295069 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 10 ≤ (0.528005617420 : ℝ)
      from by norm_num [noiseNode])) (s := (0.849240877475 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.629920847173 : ℝ) ≤ 0.699118029785 := by
    apply kappa_upper_rational (q := (0.629920847173 : ℝ)) (Q := (0.629920847173 : ℝ))
      (s := (0.776659337353 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.792659001731 : ℝ)) (R := (0.793225725985 : ℝ))
    (Q2 := (0.629920847173 : ℝ)) (T := (0.836606643427 : ℝ)) (B := retunedEnergy 10) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell11 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 11) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 11 := by
  have hk1 : kappa q ≤ 0.627086040273 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 11 ≤ (0.526806179162 : ℝ)
      from by norm_num [noiseNode])) (s := (0.849985440815 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.629106087493 : ℝ) ≤ 0.698531448679 := by
    apply kappa_upper_rational (q := (0.629106087493 : ℝ)) (Q := (0.629106087493 : ℝ))
      (s := (0.777319452143 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.792145844039 : ℝ)) (R := (0.792712568293 : ℝ))
    (Q2 := (0.629106087493 : ℝ)) (T := (0.836255600678 : ℝ)) (B := retunedEnergy 11) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell12 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 12) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 12 := by
  have hk1 : kappa q ≤ 0.626273343991 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 12 ≤ (0.525606740904 : ℝ)
      from by norm_num [noiseNode])) (s := (0.850727661427 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.628291886985 : ℝ) ≤ 0.697945557650 := by
    apply kappa_upper_rational (q := (0.628291886985 : ℝ)) (Q := (0.628291886985 : ℝ))
      (s := (0.777977701962 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.791632706466 : ℝ)) (R := (0.792199430720 : ℝ))
    (Q2 := (0.628291886985 : ℝ)) (T := (0.835904823748 : ℝ)) (B := retunedEnergy 12) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell13 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 13) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 13 := by
  have hk1 : kappa q ≤ 0.625461205551 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 13 ≤ (0.524407302646 : ℝ)
      from by norm_num [noiseNode])) (s := (0.851467545437 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.627478244974 : ℝ) ≤ 0.697360355377 := by
    apply kappa_upper_rational (q := (0.627478244974 : ℝ)) (Q := (0.627478244974 : ℝ))
      (s := (0.778634093837 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.791119588625 : ℝ)) (R := (0.791686312879 : ℝ))
    (Q2 := (0.627478244974 : ℝ)) (T := (0.835554312179 : ℝ)) (B := retunedEnergy 13) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell14 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 14) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 14 := by
  have hk1 : kappa q ≤ 0.624649624285 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 14 ≤ (0.523207864388 : ℝ)
      from by norm_num [noiseNode])) (s := (0.852205098931 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.626665160791 : ℝ) ≤ 0.696775840544 := by
    apply kappa_upper_rational (q := (0.626665160791 : ℝ)) (Q := (0.626665160791 : ℝ))
      (s := (0.779288634751 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.790606490133 : ℝ)) (R := (0.791173214387 : ℝ))
    (Q2 := (0.626665160791 : ℝ)) (T := (0.835204065518 : ℝ)) (B := retunedEnergy 14) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell15 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 15) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 15 := by
  have hk1 : kappa q ≤ 0.623838599530 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 15 ≤ (0.522008426130 : ℝ)
      from by norm_num [noiseNode])) (s := (0.852940327954 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.625852633772 : ℝ) ≤ 0.696192011843 := by
    apply kappa_upper_rational (q := (0.625852633772 : ℝ)) (Q := (0.625852633772 : ℝ))
      (s := (0.779941331641 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.790093410608 : ℝ)) (R := (0.790660134862 : ℝ))
    (Q2 := (0.625852633772 : ℝ)) (T := (0.834854083312 : ℝ)) (B := retunedEnergy 15) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

end BstLean.Part253
