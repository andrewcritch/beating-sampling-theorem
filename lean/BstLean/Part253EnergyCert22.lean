import BstLean.Part253EnergyUpper
import BstLean.Part253Retune

/-! Local upper computed-centre energy certificates. -/
namespace BstLean.Part253
open Real Set BstLean.Part130 BstLean.Part211 BstLean.Part206

theorem upperEnergyCell22 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 22) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 22 := by
  have hk1 : kappa q ≤ 0.618176953344 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 22 ≤ (0.513612358324 : ℝ)
      from by norm_num [noiseNode])) (s := (0.858022345500 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.620180489917 : ℝ) ≤ 0.692124313323 := by
    apply kappa_upper_rational (q := (0.620180489917 : ℝ)) (Q := (0.620180489917 : ℝ))
      (s := (0.784459151216 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.786502353016 : ℝ)) (R := (0.787069077270 : ℝ))
    (Q2 := (0.620180489917 : ℝ)) (T := (0.832411574900 : ℝ)) (B := retunedEnergy 22) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell23 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 23) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 23 := by
  have hk1 : kappa q ≤ 0.617370357116 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 23 ≤ (0.512412920066 : ℝ)
      from by norm_num [noiseNode])) (s := (0.858739191693 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.619372396606 : ℝ) ≤ 0.691545926964 := by
    apply kappa_upper_rational (q := (0.619372396606 : ℝ)) (Q := (0.619372396606 : ℝ))
      (s := (0.785097340668 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.785989411552 : ℝ)) (R := (0.786556135806 : ℝ))
    (Q2 := (0.619372396606 : ℝ)) (T := (0.832063692217 : ℝ)) (B := retunedEnergy 23) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell24 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 24) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 24 := by
  have hk1 : kappa q ≤ 0.616564311557 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 24 ≤ (0.511213481808 : ℝ)
      from by norm_num [noiseNode])) (s := (0.859453766074 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.618564854605 : ℝ) ≤ 0.690968215120 := by
    apply kappa_upper_rational (q := (0.618564854605 : ℝ)) (Q := (0.618564854605 : ℝ))
      (s := (0.785733746665 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.785476485652 : ℝ)) (R := (0.786043209906 : ℝ))
    (Q2 := (0.618564854605 : ℝ)) (T := (0.831716069980 : ℝ)) (B := retunedEnergy 24) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell25 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 25) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 25 := by
  have hk1 : kappa q ≤ 0.615758816034 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 25 ≤ (0.510014043550 : ℝ)
      from by norm_num [noiseNode])) (s := (0.860166074303 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.617757863283 : ℝ) ≤ 0.690391176527 := by
    apply kappa_upper_rational (q := (0.617757863283 : ℝ)) (Q := (0.617757863283 : ℝ))
      (s := (0.786368375733 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.784963574945 : ℝ)) (R := (0.785530299199 : ℝ))
    (Q2 := (0.617757863283 : ℝ)) (T := (0.831368707756 : ℝ)) (B := retunedEnergy 25) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell26 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 26) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 26 := by
  have hk1 : kappa q ≤ 0.614953869916 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 26 ≤ (0.508814605292 : ℝ)
      from by norm_num [noiseNode])) (s := (0.860876122007 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.616951422004 : ℝ) ≤ 0.689814809913 := by
    apply kappa_upper_rational (q := (0.616951422004 : ℝ)) (Q := (0.616951422004 : ℝ))
      (s := (0.787001234362 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.784450679056 : ℝ)) (R := (0.785017403310 : ℝ))
    (Q2 := (0.616951422004 : ℝ)) (T := (0.831021605104 : ℝ)) (B := retunedEnergy 26) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

theorem upperEnergyCell27 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 27) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 27 := by
  have hk1 : kappa q ≤ 0.614149472578 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 27 ≤ (0.507615167034 : ℝ)
      from by norm_num [noiseNode])) (s := (0.861583914774 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.616145530146 : ℝ) ≤ 0.689239114024 := by
    apply kappa_upper_rational (q := (0.616145530146 : ℝ)) (Q := (0.616145530146 : ℝ))
      (s := (0.787632328997 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.783937797618 : ℝ)) (R := (0.784504521872 : ℝ))
    (Q2 := (0.616145530146 : ℝ)) (T := (0.830674761593 : ℝ)) (B := retunedEnergy 27) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

end BstLean.Part253
