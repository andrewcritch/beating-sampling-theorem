import BstLean.Part264PilotCentreTerms
import BstLean.Part253CentreTerms
import BstLean.Part211Full

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part264
open BstLean.Part253
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12226 csC) (piBar (rhoBar 12226 csC)) := by
  have hr0 : 0 ≤ rhoBar 12226 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12226 csC)
  have hv0 : 0 ≤ nuR (rhoBar 12226 csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12226 csC Θ := by
  have hr0 : 0 ≤ rhoBar 12226 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12226 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12226 csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12226 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12226 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12226 csC)
  have hv0 : 0 ≤ nuR (rhoBar 12226 csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12226 csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12226 csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12226 csC 0.011 0.46 Θ ≤ 0.053506 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / 12226) ≤ 0.010801059 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12226 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036505)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010801059 + 2 * 0.737676 / 12226) := by gcongr
    _ ≤ (0.053506 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12226 12 ≤ 0.0015 := by
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar 12226 12 ≤ 0.000749634 := by
    unfold N12bar
    simp only [Nat.cast_ofNat]
    linarith
  have h10 : 0 ≤ N12bar 12226 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem pilot_radial_centre_bound {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 110.566721 ≤ R) : xiNr 12226 Θ 1.22 ≤ R := by
  have hs : √((1.22 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hn := pilot_n22_upper
  have hn0 : 0 ≤ N22bar 12226 12 := by unfold N22bar N12bar; positivity
  have hN : (110.566721 : ℝ) ≤ √12226 := le_sqrt_of_sq_le (by norm_num)
  unfold xiNr
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hR
  gcongr
  linarith

theorem pilot_full_formula_bound {Θ S X T R B : ℝ}
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.004138 + 0.0034293 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.22 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0015 + T) / 110.566721 ≤ R)
    (hB : (X + 0.053506 + R + 0.008646) ^ 2 ≤ B) :
    fullFormula 12226 12226 0.011 1.22 1.12 0.46 Θ S 1.22 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance 12226 csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, (pilot_moment_upper hw hS).trans hXsq⟩
  have hd := pilot_deviation_upper hΘ hw.2
  have hr := pilot_radial_centre_bound hΘ hT hTsq hR
  have hf : finiteEnergy 12226 12226 0.011 ≤ 0.008646 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation 12226 csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar 12226 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr 12226 Θ 1.22 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg 12226 12226 (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

end BstLean.Part264
