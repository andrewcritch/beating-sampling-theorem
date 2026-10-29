import BstLean.Part264bN12227PilotSourcePrelude
import BstLean.Part253EnergyUpper
/-! The actual computed-centre upper energy formula at 12227. -/
namespace BstLean.Part264b.N12227
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
theorem pilot_energy_upper_from_kappas {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12227 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12227 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12227 + 0.008646 / 110.566721) ^ 2 ≤ B) :
    energyRatio 12227 (gMinus 12227) q ≤ Q2 ∧
    energyUpper 12227 (gMinus 12227) (BstLean.Part211.gPlus 12227)
      (finiteEnergy 12227 12227 (11 / 1000)) q ≤ B := by
  have hs : √(kappa q + 5 / (12227 : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot 12227 q ≤ R := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hm0 : 0 ≤ meanRoot 12227 q := by unfold meanRoot; positivity
  have hR0 : 0 ≤ R := hm0.trans hm
  have hg := pilot_gMinus_lower
  have hg0 : 0 < gMinus 12227 := by linarith
  have hratio : energyRatio 12227 (gMinus 12227) q ≤ Q2 := by
    unfold energyRatio
    apply le_trans ?_ hQ2
    gcongr
  have hr0 : 0 ≤ energyRatio 12227 (gMinus 12227) q := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) hg0.le
  have hQ20 : 0 ≤ Q2 := hr0.trans hratio
  have hk := kappa_monotoneOn
    (show energyRatio 12227 (gMinus 12227) q ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩)
    (show Q2 ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩) hratio
  have hk' := hk.trans hK2
  have hk0 := (kappa_mem (by linarith : -1 ≤ energyRatio 12227 (gMinus 12227) q)
    (by linarith : energyRatio 12227 (gMinus 12227) q ≤ 1)).1
  have hgp := pilot_gPlus_upper
  have hgp0 : 0 ≤ BstLean.Part211.gPlus 12227 := le_trans zero_le_one pilot_gPlus_lower
  have ht : √(BstLean.Part211.gPlus 12227 * kappa (energyRatio 12227 (gMinus 12227) q)) ≤ T := by
    apply sqrt_le_iff.mpr
    refine ⟨hT, ?_⟩
    exact (mul_le_mul hgp hk' hk0 (by norm_num)).trans hTsq
  have ht2 : √(12 * BstLean.Part211.gPlus 12227) ≤ 3.466066 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hn : (110.566721 : ℝ) ≤ √12227 := le_sqrt_of_sq_le (by norm_num)
  have hf := pilot_finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12227 12227 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hB
  gcongr


end BstLean.Part264b.N12227
