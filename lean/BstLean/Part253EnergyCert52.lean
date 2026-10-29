import BstLean.Part253EnergyUpper
import BstLean.Part253Retune

/-! Local upper computed-centre energy certificates. -/
namespace BstLean.Part253
open Real Set BstLean.Part130 BstLean.Part211 BstLean.Part206

theorem upperEnergyCell52 {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q ≤ 1 - noiseNode 52) :
    energyRatio 12225 (gMinus 12225) q ≤ 1 ∧
    energyUpper 12225 (gMinus 12225) (gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ retunedEnergy 52 := by
  have hk1 : kappa q ≤ 0.594216123823 := by
    apply kappa_upper_rational hq0 (hq.trans (show 1 - noiseNode 52 ≤ (0.477629210584 : ℝ)
      from by norm_num [noiseNode])) (s := (0.878561515887 : ℝ))
      <;> norm_num
  have hk2 : kappa (0.596175022811 : ℝ) ≤ 0.675061101466 := by
    apply kappa_upper_rational (q := (0.596175022811 : ℝ)) (Q := (0.596175022811 : ℝ))
      (s := (0.802854496268 : ℝ)) (by norm_num) le_rfl
      <;> norm_num
  have h := energy_upper_from_kappas (q := q) (U := (0.771119395281 : ℝ)) (R := (0.771686119535 : ℝ))
    (Q2 := (0.596175022811 : ℝ)) (T := (0.822086657380 : ℝ)) (B := retunedEnergy 52) hk1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hk2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [retunedEnergy, energyTable])
  exact ⟨h.1.trans (by norm_num), h.2⟩

end BstLean.Part253
