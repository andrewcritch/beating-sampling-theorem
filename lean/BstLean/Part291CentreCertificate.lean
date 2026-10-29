import BstLean.Part291CentreTransfer

namespace BstLean.BlueprintLow
open Real Set BstLean.Part211

theorem agentCentreCertificate {n : ℕ} (hn : LowBand n) :
    CentreCertificate n n 0.011 1.25 1.14 0.46 0.528 0.1826 1.269 0.528
      (fun _ => 0.006) := by
  have hU := centreEnergyUpperBand hn.1 (q := (0.528 : ℝ)) (by norm_num) (by norm_num)
  have hM := centreMoment_nonneg hn
  apply BstLean.Part277.centreCertificate_from_momentP hn.1
    (centreMomentCertificate hn) (by norm_num) hU.1
    ((centreEMpBand hn.1 hM.1 (centreMomentBand hn) hM.2 (centreBnBand hn)).trans
      (by norm_num))
    (r := (89.442719 : ℝ)) (F := (0.010727 : ℝ))
  · convert hU.2.trans (by norm_num [agentEnergyCap] : agentEnergyCap ≤ (1 : ℝ)) using 1 <;> norm_num
  · norm_num
  · have h : (8000 : ℝ) ≤ n := by exact_mod_cast hn.1
    linarith
  · convert BstLean.Part277.finite_centre_8000 hn.1 using 1 <;> norm_num
  · norm_num
  · intro θ hθ
    have hw : θ ∈ Icc (46 / 100 : ℝ) (528 / 1000) := by
      convert hθ using 1 <;> norm_num
    convert (centreEnergyLowerBand hn.1 hw).1 using 1 <;> norm_num

end BstLean.BlueprintLow
