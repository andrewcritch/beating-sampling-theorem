import BstLean.Part264EnergyLower
import BstLean.Part211Junction

/-! Uniform energy guards complete the energy fields of a local centre certificate. -/
namespace BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211

noncomputable def centreCertificate_from_moment {n : ℕ} (hn : 12225 ≤ n)
    {thetaHi S qWorld : ℝ} (hhi : thetaHi ≤ 0.532)
    (M : MomentCertificate n 0.011 1.22 1.12 (0.46) thetaHi S (fun _ => 0.006))
    (hq : qWorld ∈ Icc (-1 : ℝ) 1)
    (hDomain : BstLean.Part206.energyRatio n (gMinus n) qWorld ≤ 1)
    (hGap : BstLean.Part154.eMP n 0.011
      (momentAllowance n BstLean.Part154.csC 0.011 1.22 1.12 thetaHi S)
      (BstLean.Part154.bN n BstLean.Part154.csC thetaHi) ≤ 1 / 10)
    (hUpper : BstLean.Part206.energyUpper n (gMinus n) (BstLean.Part211.gPlus n)
      (finiteEnergy n n 0.011) qWorld ≤ 1) :
    CentreCertificate n n 0.011 1.22 1.12 (0.46) thetaHi S 1.22 qWorld
      (fun _ => 0.006) where
  toMomentCertificate := M
  delta_upper := by norm_num
  signal_domain := hq
  energy_domain := hDomain
  energy_root := energy_root_guard hn
  energy_lower := by have := gMinus_lower hn; linarith
  energy_upper := by have := gPlus_upper hn; linarith
  relative_gap := hGap
  finite_guard := finite_guard hn
  lower_root := fun _ hθ => le_trans (by norm_num : (0 : ℝ) ≤ 0.76589)
    (mean_lower_window hn ⟨hθ.1,hθ.2.trans hhi⟩).1
  lower_bracket := fun _ hθ => (energy_lower_data hn ⟨hθ.1,hθ.2.trans hhi⟩).1
  lower_guard := by
    intro θ hθ
    have h := (energy_lower_data hn ⟨hθ.1,hθ.2.trans hhi⟩).2.1
    convert le_trans (by norm_num : (0 : ℝ) ≤ 0.81583) h using 1 <;> norm_num
  upper_clip := hUpper

end BstLean.Part264
