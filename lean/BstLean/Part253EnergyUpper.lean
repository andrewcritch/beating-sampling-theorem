import BstLean.Part253EnergyLower

/-! Rational upper certificates for the local computed-centre energy. -/
namespace BstLean.Part253
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206

theorem kappa_upper_rational {q Q s K : ℝ} (hq : 0 ≤ q) (hQ : q ≤ Q)
    (hQ1 : Q ≤ 3 / 4) (hs : 0 ≤ s) (hsq : 1 - Q ^ 2 ≤ s ^ 2)
    (hK : (s + Q * (3141593 / 2000000 + Q + Q ^ 3 / 6 + 3 * Q ^ 5 / 40 + Q ^ 7 / 10)) /
      (3141592 / 1000000) ≤ K) : kappa q ≤ K := by
  have hQ0 : 0 ≤ Q := hq.trans hQ
  have hk := kappa_monotoneOn (show q ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩)
    (show Q ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩) hQ
  have hu := sn_kappa_le hQ0 hQ1 (sqrt_le_iff.mpr ⟨hs, hsq⟩)
  apply hk.trans (hu.trans ?_)
  convert hK using 1 <;> ring

theorem energy_upper_from_kappas {q K1 U R Q2 K2 T B : ℝ}
    (hK1 : kappa q ≤ K1) (hU : 0 ≤ U) (hUsq : K1 + 5 / 12225 ≤ U ^ 2)
    (hR : U + 2 * 3.464102 / 12225 ≤ R)
    (hQ2 : R ^ 2 / 0.99886685 ≤ Q2) (hQ21 : Q2 ≤ 3 / 4)
    (hK2 : kappa Q2 ≤ K2) (hK20 : 0 ≤ K2)
    (hT : 0 ≤ T) (hTsq : 1.00113378 * K2 ≤ T ^ 2)
    (hB : (T + 2 * 3.466066 / 12225 + 0.008646 / 110.566721) ^ 2 ≤ B) :
    energyRatio 12225 (gMinus 12225) q ≤ Q2 ∧
    energyUpper 12225 (gMinus 12225) (BstLean.Part211.gPlus 12225)
      (finiteEnergy 12225 12225 (11 / 1000)) q ≤ B := by
  have hs : √(kappa q + 5 / (12225 : ℝ)) ≤ U :=
    sqrt_le_iff.mpr ⟨hU, by linarith⟩
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have hm : meanRoot 12225 q ≤ R := by
    unfold meanRoot
    simp only [Nat.cast_ofNat]
    linarith
  have hm0 : 0 ≤ meanRoot 12225 q := by unfold meanRoot; positivity
  have hR0 : 0 ≤ R := hm0.trans hm
  have hg := gMinus_lower
  have hg0 : 0 < gMinus 12225 := by linarith
  have hratio : energyRatio 12225 (gMinus 12225) q ≤ Q2 := by
    unfold energyRatio
    apply le_trans ?_ hQ2
    gcongr
  have hr0 : 0 ≤ energyRatio 12225 (gMinus 12225) q := by
    unfold energyRatio
    exact div_nonneg (sq_nonneg _) hg0.le
  have hQ20 : 0 ≤ Q2 := hr0.trans hratio
  have hk := kappa_monotoneOn
    (show energyRatio 12225 (gMinus 12225) q ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩)
    (show Q2 ∈ Icc (-1 : ℝ) 1 from ⟨by linarith, by linarith⟩) hratio
  have hk' := hk.trans hK2
  have hk0 := (kappa_mem (by linarith : -1 ≤ energyRatio 12225 (gMinus 12225) q)
    (by linarith : energyRatio 12225 (gMinus 12225) q ≤ 1)).1
  have hgp := gPlus_upper
  have hgp0 : 0 ≤ BstLean.Part211.gPlus 12225 := le_trans zero_le_one gPlus_lower
  have ht : √(BstLean.Part211.gPlus 12225 * kappa (energyRatio 12225 (gMinus 12225) q)) ≤ T := by
    apply sqrt_le_iff.mpr
    refine ⟨hT, ?_⟩
    exact (mul_le_mul hgp hk' hk0 (by norm_num)).trans hTsq
  have ht2 : √(12 * BstLean.Part211.gPlus 12225) ≤ 3.466066 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hn : (110.566721 : ℝ) ≤ √12225 := le_sqrt_of_sq_le (by norm_num)
  have hf := finite_centre_upper
  have hf0 := finiteEnergy_nonneg 12225 12225 (by norm_num : (0 : ℝ) ≤ 11 / 1000)
  refine ⟨hratio, ?_⟩
  unfold energyUpper
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hB
  gcongr

end BstLean.Part253
