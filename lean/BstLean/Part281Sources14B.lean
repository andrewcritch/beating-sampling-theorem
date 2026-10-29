import BstLean.Part281Sources14A
import BstLean.Part211Full
import BstLean.Part211MA
import BstLean.Part211Parallel
import BstLean.Part253CentreConstants
import BstLean.Part253CentreFormula
import BstLean.Part253CentreTerms
import BstLean.Part253Data
import BstLean.Part253Exp
import BstLean.Part253ExpFraction
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part264HS
import BstLean.Part264PilotCentreConstants
import BstLean.Part264PilotCentreTerms
import BstLean.Part277Frame
import BstLean.Part277Instances
import BstLean.Part281Direction
import BstLean.Part281EnergyLower
import BstLean.Part281Group14
import BstLean.Part281Groups
import BstLean.Part281SourceCommon
import BstLean.Part281TailBounds
import BstLean.Part281UniformEnergy
namespace BstLean.Part281.N12222
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
theorem pilot_wn_upper : wn 12222 ≤ (1.036508968954 : ℝ) := by
  have hr : (110.553154636129 : ℝ) ≤ √(12222 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.553154636129 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : finiteEnergy 12222 12222 (11 / 1000) ≤ (0.008771 : ℝ) := by
  convert BstLean.Part277.finite_centre_11883 (by norm_num : 11883 ≤ 12222) using 1 <;> norm_num
noncomputable def pilotParallelCap : ℝ := BstLean.Part281.scalarRow12222.xi
end BstLean.Part281.N12222

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part281.N12222
open BstLean.Part253
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036508968953 : ℝ) ≤ wn 12222 := by
  have hn : √(12222 : ℝ) ≤ 110.553154636130 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12222 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.553154636130 ≤ 2 / √(12222 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261908695 : ℝ) ≤ rhoBar 12222 csC ∧
    rhoBar 12222 csC ≤ 0.000261909100 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036508968953 : ℝ) / (1.295212 * 12222) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036508968954 : ℝ) / (1.29521 * 12222) := by gcongr
      _ ≤ (0.000261909100 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12222 csC) ≤ 0.001047704997 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12222 csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part281.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12222 csC) (piBar (rhoBar 12222 csC)) ≤ 0.000200048308 ∧
    cc1 (rhoBar 12222 csC) (piBar (rhoBar 12222 csC)) ≤ 0.000127291990 ∧
    cc2 (rhoBar 12222 csC) ≤ 0.000073893883 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12222 csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12222 csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12222 csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12222 csC * nuR (rhoBar 12222 csC)) ≤ 0.000523835349 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261909100 : ℝ) * 0.001047704997 := by gcongr
      _ ≤ (0.000523835349 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12222 csC) * nuR (rhoBar 12222 csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001047704997 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12222 csC) * rhoBar 12222 csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261909100 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261909100 / 2 + 0.399 * 0.001047704997 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000200048308 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523835349 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127291990 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261909100 / 1.414213562 := by gcongr
      _ ≤ (0.000073893883 : ℝ) := by norm_num

end BstLean.Part281.N12222

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part281.N12222
open BstLean.Part253
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12222 csC) (piBar (rhoBar 12222 csC)) ≤ 1.72824E-7 := by
  have hr0 : 0 ≤ rhoBar 12222 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12222 csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12222 csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12222 csC) (piBar (rhoBar 12222 csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12222 csC) (piBar (rhoBar 12222 csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12222 csC) := by unfold cc2; positivity
  have hc0 := pilot_cc_bounds.1
  have hc1 := pilot_cc_bounds.2.1
  have hc2 := pilot_cc_bounds.2.2
  have hs : √(2 / π) ≤ 0.797885 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ pi_pos).mpr
    linarith [pi_gt_d6]
  unfold QB
  calc
    _ ≤ (0.000200048308 : ℝ) ^ 2 + 0.000127291990 ^ 2 + 3 * 0.000073893883 ^ 2 +
        2 * 0.797885 * 0.000200048308 * 0.000127291990 + 2 * 0.000200048308 * 0.000073893883 +
        4 * 0.797885 * 0.000127291990 * 0.000073893883 := by gcongr
    _ ≤ (1.72824E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12222 csC Θ ≤ 0.002735817932 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12222 csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12222 csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12222 csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12222 csC) (piBar (rhoBar 12222 csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12222 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036508968954 * 1.72824E-7 / (0.000261908695 : ℝ) := by gcongr
    _ ≤ 0.002735817932 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12222 csC Θ ≤ 0.003037590006 + 0.000691295703 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12222 csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12222 csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12222 csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036508968954 : ℝ) * ((2 * Θ * 0.000261909100 +
        (6863 / 10000) * 0.000261909100 * 12222 * 0.001047704997) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003037590006 + 0.000691295703 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09430 : ℝ) ≤ gap 2 (rhoBar 12222 csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997300 : ℝ) ≤ √(1 - 2 * rhoBar 12222 csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12222 0.011 Θ ∧ gammaRatio 12222 0.011 Θ ≤ 0.000090037576 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12222 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036508968954 : ℝ) * 0.525 / ((1 - 0.011) * 12222) := by gcongr
      _ ≤ (0.000090037576 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.05504 : ℝ) ≤ gap 1 (gammaRatio 12222 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.9999535 : ℝ) ≤ √(1 - gammaRatio 12222 0.011 Θ) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.12 ≤ 0.94491119 := by
    calc
      _ ≤ (1 : ℝ) / 1.05830052 := by gcongr
      _ ≤ (0.94491119 : ℝ) := by norm_num
  unfold gap
  rw [one_mul]
  linarith

theorem pilot_bad_upper {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    badAllowance 12222 csC 0.011 1.22 1.12 Θ ≤ 0.001130056561 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12222 csC) 1.22 ≤ 4.5754E-8 := by
    have he : (16.9 : ℝ) ≤ gap 2 (rhoBar 12222 csC) 1.22 ^ 2 / (2 * rhoBar 12222 csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12222 csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part281.Tails.exp_minus_16_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12222 0.011 Θ) 1.12 ≤ 5.0566E-8 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12222 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12222 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12222 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part281.Tails.exp_minus_16_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12222 csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12222 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036508968954 : ℝ) * 12222 *
        (4.5754E-8 / 1.1045361 + 5.0566E-8 / 1.05830052) := by gcongr
    _ ≤ (0.001130056561 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12222 csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004167646567 + 0.003427113635 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part281.N12222

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part281.N12222
open BstLean.Part253
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12222 csC) (piBar (rhoBar 12222 csC)) := by
  have hr0 : 0 ≤ rhoBar 12222 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12222 csC)
  have hv0 : 0 ≤ nuR (rhoBar 12222 csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12222 csC Θ := by
  have hr0 : 0 ≤ rhoBar 12222 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12222 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12222 csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12222 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12222 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12222 csC)
  have hv0 : 0 ≤ nuR (rhoBar 12222 csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12222 csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12222 csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12222 csC 0.011 0.46 Θ ≤ 0.053512031435 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / 12222) ≤ 0.010802383569 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12222 * Θ) ≤ 0.737676899938 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036508968954)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010802383569 + 2 * 0.737676899938 / 12222) := by gcongr
    _ ≤ (0.053512031435 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12222 12 ≤ 0.0016 := by
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar 12222 12 ≤ 0.000749817706 := by
    unfold N12bar
    simp only [Nat.cast_ofNat]
    linarith
  have h10 : 0 ≤ N12bar 12222 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem pilot_radial_centre_bound {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.25 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0016 + T) / 110.553154636129 ≤ R) : xiNr 12222 Θ 1.25 ≤ R := by
  have hs : √((1.25 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hn := pilot_n22_upper
  have hn0 : 0 ≤ N22bar 12222 12 := by unfold N22bar N12bar; positivity
  have hN : (110.553154636129 : ℝ) ≤ √(12222 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold xiNr
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hR
  gcongr
  linarith

theorem pilot_full_formula_bound {Θ S X T R B : ℝ}
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.004167646567 + 0.003427113635 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.25 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0016 + T) / 110.553154636129 ≤ R)
    (hB : (X + 0.053512031435 + R + 0.008771) ^ 2 ≤ B) :
    fullFormula 12222 12222 0.011 1.22 1.12 0.46 Θ S 1.25 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance 12222 csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, (pilot_moment_upper hw hS).trans hXsq⟩
  have hd := pilot_deviation_upper hΘ hw.2
  have hr := pilot_radial_centre_bound hΘ hT hTsq hR
  have hf : finiteEnergy 12222 12222 0.011 ≤ 0.008771 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation 12222 csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar 12222 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr 12222 Θ 1.25 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg 12222 12222 (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

end BstLean.Part281.N12222

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part281.N12222
open BstLean.Part253
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481106291 : ℝ) ≤ plow 12222 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12222) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053553101226)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001436304415) : eMP 12222 0.011 xi bn ≤ 0.001235884040 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12222 : ℝ) * (1 - 0.011))) ≤ 0.000610982713 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001436304415 / (12222 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610982713 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610982713 : ℝ) + 3.141593 * 0.053553101226 / (12222 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001235884040 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053553101226)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001436304415) : PiBarMP 12222 12 0.011 xi bn ≤ 0.164408098106 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12222 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037898607033 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (109.943430908808 : ℝ) ≤ √((12222 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.553154636129 : ℝ) ≤ √(12222 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12222) ≤ 0.126024520138 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037898607033 + 0.053553101226 * 1.772454 / (2 * (109.943430908808 : ℝ))) * (1 + 0.001235884040) +
        8 / (12222 * 110.553154636129) + 0.126024520138 := by gcongr
    _ ≤ (0.164408098106 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053553101226)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001436304415) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284927461401) :
    parallelOracle 12222 0.011 xi bn cd ≤ 0.165441199590 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12222 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12222 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481106291 : ℝ) ≤ plow 12222 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.553154636129 : ℝ) ≤ √(12222 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284927461401 : ℝ) / (2 * 0.560481106291 * 110.553154636129)) * 0.164408098106 +
        0.284927461401 ^ 2 / (2 * 0.560481106291 * 110.553154636129) := by gcongr
    _ ≤ (0.165441199590 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053553101226) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001436304415)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284927461401) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12222 12222 0.011 xi bn cd Θ 1.25 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481106291 : ℝ) ≤ plow 12222 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.553154636129 : ℝ) ≤ √(12222 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12222 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.25 : ℝ) * Θ) ≤ 0.810092587301 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12222 Θ 1.25 ≤ 0.012084074776 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0016 + 0.810092587301) / 110.553154636129 := by gcongr <;> linarith
      _ ≤ (0.012084074776 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12222 Θ 1.25 := by unfold xiNr; positivity
  have hf : finiteEnergy 12222 12222 0.011 ≤ 0.008771 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12222 12222 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12222 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12222 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12222 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12222 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165441199590 + 0.012084074776 + (0.008771 : ℝ) *
        (1 + 2 * (0.284927461401 + 0.012084074776) / (0.560481106291 * 110.553154636129))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part281.scalarRow12222]

end BstLean.Part281.N12222

/-! The original eight local profiles supply actual 12222 moment certificates. -/
namespace BstLean.Part281.N12222
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part281.Groups

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : BstLean.Part281.Groups.NeededGroup g) :
    MomentCertificate 12222 0.011 1.22 1.12 0.46 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part281.Groups.group_scalar hg
  exact {
    delta_nonneg := by norm_num
    delta_lt := by norm_num
    k_gt := by norm_num
    k3_gt := by norm_num
    theta_lower := by norm_num
    v_pos := by intro θ hθ; norm_num
    supremum := fun θ hθ => by
      have hθ0 : 0 < θ := lt_of_lt_of_le (by norm_num) hθ.1
      have hθ1 : θ ≤ 1 := hθ.2.trans (G.window.2.trans (by norm_num))
      exact (mul_le_mul_of_nonneg_right (BstLean.Part281.Groups.hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part281.Groups.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : BstLean.Part281.Groups.NeededGroup g) :
    0 ≤ momentAllowance 12222 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g) ∧
    momentAllowance 12222 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g) ≤ 0.053553101226 ∧
    0 ≤ bN 12222 csC (BstLean.Part281.Groups.groupTheta g) ∧ bN 12222 csC (BstLean.Part281.Groups.groupTheta g) ≤ 0.001436304415 := by
  have G := BstLean.Part281.Groups.group_scalar hg
  have hΘ : 0 ≤ BstLean.Part281.Groups.groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : BstLean.Part281.Groups.NeededGroup g) :
    parallelFormula 12222 12222 0.011
      (momentAllowance 12222 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g))
      (bN 12222 csC (BstLean.Part281.Groups.groupTheta g))
      (√(momentAllowance 12222 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g)) +
        sharpDeviation 12222 csC 0.011 0.46 (BstLean.Part281.Groups.groupTheta g)) (BstLean.Part281.Groups.groupTheta g) 1.25 ≤ pilotParallelCap := by
  have G := BstLean.Part281.Groups.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ BstLean.Part281.Groups.groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12222 csC 0.011 0.46 (BstLean.Part281.Groups.groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12222 csC 0.011 1.22 1.12
      (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g)) ≤ 0.231415429966 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : BstLean.Part281.Groups.NeededGroup g) :
    eMP 12222 0.011
      (momentAllowance 12222 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g))
      (bN 12222 csC (BstLean.Part281.Groups.groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part281.N12222
namespace BstLean.Part281.N12222
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.087091888192
  | 2 => 0.088067376975
  | 3 => 0.089046222233
  | 4 => 0.090030997301
  | 5 => 0.091024768414
  | 6 => 0.092031161628
  | 7 => 0.093054434941
  | 8 => 0.094099555469
  | _ => 0

theorem pilot_fullGroup1 :
    fullFormula 12222 12222 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 1) (BstLean.Part281.Groups.groupProfile 1) 1.25 ≤ pilotGroupCentre 1 := by
  apply pilot_full_formula_bound (X := (0.220846407282 : ℝ)) (T := (0.770098081416 : ℝ)) (R := (0.011264246913 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup2 :
    fullFormula 12222 12222 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 2) (BstLean.Part281.Groups.groupProfile 2) 1.25 ≤ pilotGroupCentre 2 := by
  apply pilot_full_formula_bound (X := (0.222413647311 : ℝ)) (T := (0.775935939689 : ℝ)) (R := (0.011382469075 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup3 :
    fullFormula 12222 12222 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 3) (BstLean.Part281.Groups.groupProfile 3) 1.25 ≤ pilotGroupCentre 3 := by
  apply pilot_full_formula_bound (X := (0.223960509905 : ℝ)) (T := (0.781730202020 : ℝ)) (R := (0.011500296884 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup4 :
    fullFormula 12222 12222 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 4) (BstLean.Part281.Groups.groupProfile 4) 1.25 ≤ pilotGroupCentre 4 := by
  apply pilot_full_formula_bound (X := (0.225487197159 : ℝ)) (T := (0.787481832331 : ℝ)) (R := (0.011617739078 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup5 :
    fullFormula 12222 12222 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 5) (BstLean.Part281.Groups.groupProfile 5) 1.25 ≤ pilotGroupCentre 5 := by
  apply pilot_full_formula_bound (X := (0.226993904812 : ℝ)) (T := (0.793191757238 : ℝ)) (R := (0.011734804028 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup6 :
    fullFormula 12222 12222 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 6) (BstLean.Part281.Groups.groupProfile 6) 1.25 ≤ pilotGroupCentre 6 := by
  apply pilot_full_formula_bound (X := (0.228480823096 : ℝ)) (T := (0.798860870240 : ℝ)) (R := (0.011851499809 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup7 :
    fullFormula 12222 12222 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 7) (BstLean.Part281.Groups.groupProfile 7) 1.25 ≤ pilotGroupCentre 7 := by
  apply pilot_full_formula_bound (X := (0.229948137513 : ℝ)) (T := (0.804490035675 : ℝ)) (R := (0.011967834256 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup8 :
    fullFormula 12222 12222 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 8) (BstLean.Part281.Groups.groupProfile 8) 1.25 ≤ pilotGroupCentre 8 := by
  apply pilot_full_formula_bound (X := (0.231396027778 : ℝ)) (T := (0.810080085548 : ℝ)) (R := (0.012083814886 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_group_full {g : Fin 10} (hg : BstLean.Part281.Groups.NeededGroup g) :
    fullFormula 12222 12222 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g) 1.25 ≤ pilotGroupCentre g := by
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => exact pilot_fullGroup1
  | ⟨2,h⟩ => exact pilot_fullGroup2
  | ⟨3,h⟩ => exact pilot_fullGroup3
  | ⟨4,h⟩ => exact pilot_fullGroup4
  | ⟨5,h⟩ => exact pilot_fullGroup5
  | ⟨6,h⟩ => exact pilot_fullGroup6
  | ⟨7,h⟩ => exact pilot_fullGroup7
  | ⟨8,h⟩ => exact pilot_fullGroup8
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)
end BstLean.Part281.N12222
namespace BstLean.Part281.N12222
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part281 (scalarRow12222 cell12222)
open BstLean.Part281.Groups (groupTheta groupProfile NeededGroup centreGroup)
theorem sourceCell10 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨10,by decide⟩).lower ∧ (scalarRow12222.table ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (scalarRow12222.table ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((471994723014450290600389/1000000000000000000000000) : ℝ) ∧ ((473194195315895319660429/1000000000000000000000000) : ℝ) ≤ (0.474440844 : ℝ) ∧
      ((473194195315895319660429/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((1360810753/15625000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1402253348081409/2000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((471994723014450290600389/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((1360810753/15625000000) : ℝ) = (0.087091888192 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((471994723014450290600389/1000000000000000000000000) : ℚ) ∧ ((473194195315895319660429/1000000000000000000000000) : ℚ) ≤ (0.474440844 : ℚ) ∧
      ((473194195315895319660429/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((1360810753/15625000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1402253348081409/2000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((471994723014450290600389/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((1360810753/15625000000) : ℚ) = (0.087091888192 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((471994723014450290600389/1000000000000000000000000) : ℝ) ∧ ((473194195315895319660429/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
      ((473194195315895319660429/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((1360810753/15625000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1402253348081409/2000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((471994723014450290600389/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((1360810753/15625000000) : ℝ) = pilotGroupCentre (centreGroup ⟨10,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy10 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨10,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨10,by decide⟩).lower) ≤ (scalarRow12222.table ⟨10,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((471994723014450290600389/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((471994723014450290600389/1000000000000000000000000) : ℝ)) ≤ ((1402253348081409/2000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy10 (n := 12222) (by norm_num)
    (q := 1 - ((471994723014450290600389/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell11 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨11,by decide⟩).lower ∧ (scalarRow12222.table ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (scalarRow12222.table ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((118298548828973829915107/250000000000000000000000) : ℝ) ∧ ((118598416904335087180117/250000000000000000000000) : ℝ) ≤ (0.474440844 : ℝ) ∧
      ((118598416904335087180117/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((1360810753/15625000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3502713138673043/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((118298548828973829915107/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((1360810753/15625000000) : ℝ) = (0.087091888192 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((118298548828973829915107/250000000000000000000000) : ℚ) ∧ ((118598416904335087180117/250000000000000000000000) : ℚ) ≤ (0.474440844 : ℚ) ∧
      ((118598416904335087180117/250000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((1360810753/15625000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3502713138673043/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((118298548828973829915107/250000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((1360810753/15625000000) : ℚ) = (0.087091888192 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((118298548828973829915107/250000000000000000000000) : ℝ) ∧ ((118598416904335087180117/250000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
      ((118598416904335087180117/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((1360810753/15625000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3502713138673043/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((118298548828973829915107/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((1360810753/15625000000) : ℝ) = pilotGroupCentre (centreGroup ⟨11,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy11 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨11,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨11,by decide⟩).lower) ≤ (scalarRow12222.table ⟨11,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((118298548828973829915107/250000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((118298548828973829915107/250000000000000000000000) : ℝ)) ≤ ((3502713138673043/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy11 (n := 12222) (by norm_num)
    (q := 1 - ((118298548828973829915107/250000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell12 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨12,by decide⟩).lower ∧ (scalarRow12222.table ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (scalarRow12222.table ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((474393667617340348720467/1000000000000000000000000) : ℝ) ∧ ((475593139918785377780507/1000000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((475593139918785377780507/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((3522695079/40000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6999592396984119/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((474393667617340348720467/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((3522695079/40000000000) : ℝ) = (0.088067376975 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((474393667617340348720467/1000000000000000000000000) : ℚ) ∧ ((475593139918785377780507/1000000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((475593139918785377780507/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((3522695079/40000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6999592396984119/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((474393667617340348720467/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((3522695079/40000000000) : ℚ) = (0.088067376975 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((474393667617340348720467/1000000000000000000000000) : ℝ) ∧ ((475593139918785377780507/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
      ((475593139918785377780507/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((3522695079/40000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6999592396984119/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((474393667617340348720467/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((3522695079/40000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨12,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy12 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨12,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨12,by decide⟩).lower) ≤ (scalarRow12222.table ⟨12,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((474393667617340348720467/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((474393667617340348720467/1000000000000000000000000) : ℝ)) ≤ ((6999592396984119/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy12 (n := 12222) (by norm_num)
    (q := 1 - ((474393667617340348720467/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell13 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨13,by decide⟩).lower ∧ (scalarRow12222.table ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (scalarRow12222.table ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((237796569959392688890253/500000000000000000000000) : ℝ) ∧ ((238396306110115203420273/500000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((238396306110115203420273/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((3522695079/40000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6993765088265143/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((237796569959392688890253/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((3522695079/40000000000) : ℝ) = (0.088067376975 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((237796569959392688890253/500000000000000000000000) : ℚ) ∧ ((238396306110115203420273/500000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((238396306110115203420273/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((3522695079/40000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6993765088265143/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((237796569959392688890253/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((3522695079/40000000000) : ℚ) = (0.088067376975 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((237796569959392688890253/500000000000000000000000) : ℝ) ∧ ((238396306110115203420273/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
      ((238396306110115203420273/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((3522695079/40000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6993765088265143/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((237796569959392688890253/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((3522695079/40000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨13,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy13 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨13,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨13,by decide⟩).lower) ≤ (scalarRow12222.table ⟨13,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((237796569959392688890253/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((237796569959392688890253/500000000000000000000000) : ℝ)) ≤ ((6993765088265143/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy13 (n := 12222) (by norm_num)
    (q := 1 - ((237796569959392688890253/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell14 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨14,by decide⟩).lower ∧ (scalarRow12222.table ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (scalarRow12222.table ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((95358522444046081368109/200000000000000000000000) : ℝ) ∧ ((95598416904335087180117/200000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((95598416904335087180117/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((3522695079/40000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((10918663031527/15625000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((95358522444046081368109/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((3522695079/40000000000) : ℝ) = (0.088067376975 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((95358522444046081368109/200000000000000000000000) : ℚ) ∧ ((95598416904335087180117/200000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((95598416904335087180117/200000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((3522695079/40000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((10918663031527/15625000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((95358522444046081368109/200000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((3522695079/40000000000) : ℚ) = (0.088067376975 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((95358522444046081368109/200000000000000000000000) : ℝ) ∧ ((95598416904335087180117/200000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
      ((95598416904335087180117/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((3522695079/40000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((10918663031527/15625000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((95358522444046081368109/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((3522695079/40000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨14,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy14 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨14,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨14,by decide⟩).lower) ≤ (scalarRow12222.table ⟨14,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((95358522444046081368109/200000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((95358522444046081368109/200000000000000000000000) : ℝ)) ≤ ((10918663031527/15625000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy14 (n := 12222) (by norm_num)
    (q := 1 - ((95358522444046081368109/200000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell15 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨15,by decide⟩).lower ∧ (scalarRow12222.table ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (scalarRow12222.table ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((59749010565209429487573/125000000000000000000000) : ℝ) ∧ ((29949472301445029060039/62500000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((29949472301445029060039/62500000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((3522695079/40000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6982130141752497/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((59749010565209429487573/125000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((3522695079/40000000000) : ℝ) = (0.088067376975 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((59749010565209429487573/125000000000000000000000) : ℚ) ∧ ((29949472301445029060039/62500000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((29949472301445029060039/62500000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((3522695079/40000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6982130141752497/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((59749010565209429487573/125000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((3522695079/40000000000) : ℚ) = (0.088067376975 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((59749010565209429487573/125000000000000000000000) : ℝ) ∧ ((29949472301445029060039/62500000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
      ((29949472301445029060039/62500000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((3522695079/40000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6982130141752497/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((59749010565209429487573/125000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((3522695079/40000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨15,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy15 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨15,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨15,by decide⟩).lower) ≤ (scalarRow12222.table ⟨15,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((59749010565209429487573/125000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((59749010565209429487573/125000000000000000000000) : ℝ)) ≤ ((6982130141752497/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy15 (n := 12222) (by norm_num)
    (q := 1 - ((59749010565209429487573/125000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell16 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨16,by decide⟩).lower ∧ (scalarRow12222.table ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (scalarRow12222.table ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((479191556823120464960623/1000000000000000000000000) : ℝ) ∧ ((480391029124565494020663/1000000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((480391029124565494020663/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((3522695079/40000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6976322482066327/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((479191556823120464960623/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((3522695079/40000000000) : ℝ) = (0.088067376975 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((479191556823120464960623/1000000000000000000000000) : ℚ) ∧ ((480391029124565494020663/1000000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((480391029124565494020663/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((3522695079/40000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6976322482066327/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((479191556823120464960623/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((3522695079/40000000000) : ℚ) = (0.088067376975 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((479191556823120464960623/1000000000000000000000000) : ℝ) ∧ ((480391029124565494020663/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
      ((480391029124565494020663/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((3522695079/40000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6976322482066327/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((479191556823120464960623/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((3522695079/40000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨16,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy16 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨16,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨16,by decide⟩).lower) ≤ (scalarRow12222.table ⟨16,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((479191556823120464960623/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((479191556823120464960623/1000000000000000000000000) : ℝ)) ≤ ((6976322482066327/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy16 (n := 12222) (by norm_num)
    (q := 1 - ((479191556823120464960623/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell17 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨17,by decide⟩).lower ∧ (scalarRow12222.table ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (scalarRow12222.table ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((240195514562282747010331/500000000000000000000000) : ℝ) ∧ ((240795250713005261540351/500000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((240795250713005261540351/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((3522695079/40000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6970521350237597/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((240195514562282747010331/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((3522695079/40000000000) : ℝ) = (0.088067376975 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((240195514562282747010331/500000000000000000000000) : ℚ) ∧ ((240795250713005261540351/500000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((240795250713005261540351/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((3522695079/40000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6970521350237597/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((240195514562282747010331/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((3522695079/40000000000) : ℚ) = (0.088067376975 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((240195514562282747010331/500000000000000000000000) : ℝ) ∧ ((240795250713005261540351/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
      ((240795250713005261540351/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((3522695079/40000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6970521350237597/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((240195514562282747010331/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((3522695079/40000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨17,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy17 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨17,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨17,by decide⟩).lower) ≤ (scalarRow12222.table ⟨17,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((240195514562282747010331/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((240195514562282747010331/500000000000000000000000) : ℝ)) ≤ ((6970521350237597/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy17 (n := 12222) (by norm_num)
    (q := 1 - ((240195514562282747010331/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell18 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨18,by decide⟩).lower ∧ (scalarRow12222.table ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (scalarRow12222.table ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((481590501426010523080701/1000000000000000000000000) : ℝ) ∧ ((482789973727455552140741/1000000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((482789973727455552140741/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89046222233/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1741181683857039/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((481590501426010523080701/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((89046222233/1000000000000) : ℝ) = (0.089046222233 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((481590501426010523080701/1000000000000000000000000) : ℚ) ∧ ((482789973727455552140741/1000000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((482789973727455552140741/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((89046222233/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1741181683857039/2500000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((481590501426010523080701/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((89046222233/1000000000000) : ℚ) = (0.089046222233 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((481590501426010523080701/1000000000000000000000000) : ℝ) ∧ ((482789973727455552140741/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
      ((482789973727455552140741/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89046222233/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1741181683857039/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((481590501426010523080701/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((89046222233/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨18,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy18 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨18,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨18,by decide⟩).lower) ≤ (scalarRow12222.table ⟨18,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((481590501426010523080701/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((481590501426010523080701/1000000000000000000000000) : ℝ)) ≤ ((1741181683857039/2500000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy18 (n := 12222) (by norm_num)
    (q := 1 - ((481590501426010523080701/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell19 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨19,by decide⟩).lower ∧ (scalarRow12222.table ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (scalarRow12222.table ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((24139498686372777607037/50000000000000000000000) : ℝ) ∧ ((24199472301445029060039/50000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((24199472301445029060039/50000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89046222233/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6958938626842607/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((24139498686372777607037/50000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((89046222233/1000000000000) : ℝ) = (0.089046222233 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((24139498686372777607037/50000000000000000000000) : ℚ) ∧ ((24199472301445029060039/50000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((24199472301445029060039/50000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((89046222233/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6958938626842607/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((24139498686372777607037/50000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((89046222233/1000000000000) : ℚ) = (0.089046222233 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((24139498686372777607037/50000000000000000000000) : ℝ) ∧ ((24199472301445029060039/50000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
      ((24199472301445029060039/50000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89046222233/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6958938626842607/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((24139498686372777607037/50000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((89046222233/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨19,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy19 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨19,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨19,by decide⟩).lower) ≤ (scalarRow12222.table ⟨19,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((24139498686372777607037/50000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((24139498686372777607037/50000000000000000000000) : ℝ)) ≤ ((6958938626842607/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy19 (n := 12222) (by norm_num)
    (q := 1 - ((24139498686372777607037/50000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell20 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨20,by decide⟩).lower ∧ (scalarRow12222.table ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (scalarRow12222.table ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((483989446028900581200779/1000000000000000000000000) : ℝ) ∧ ((485188918330345610260819/1000000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((485188918330345610260819/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89046222233/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6953157013728039/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((483989446028900581200779/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((89046222233/1000000000000) : ℝ) = (0.089046222233 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((483989446028900581200779/1000000000000000000000000) : ℚ) ∧ ((485188918330345610260819/1000000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((485188918330345610260819/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((89046222233/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6953157013728039/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((483989446028900581200779/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((89046222233/1000000000000) : ℚ) = (0.089046222233 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((483989446028900581200779/1000000000000000000000000) : ℝ) ∧ ((485188918330345610260819/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
      ((485188918330345610260819/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89046222233/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6953157013728039/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((483989446028900581200779/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((89046222233/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨20,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy20 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨20,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨20,by decide⟩).lower) ≤ (scalarRow12222.table ⟨20,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((483989446028900581200779/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((483989446028900581200779/1000000000000000000000000) : ℝ)) ≤ ((6953157013728039/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy20 (n := 12222) (by norm_num)
    (q := 1 - ((483989446028900581200779/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell21 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨21,by decide⟩).lower ∧ (scalarRow12222.table ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (scalarRow12222.table ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((242594459165172805130409/500000000000000000000000) : ℝ) ∧ ((243194195315895319660429/500000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((243194195315895319660429/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89046222233/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6947381885373761/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((242594459165172805130409/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((89046222233/1000000000000) : ℝ) = (0.089046222233 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((242594459165172805130409/500000000000000000000000) : ℚ) ∧ ((243194195315895319660429/500000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((243194195315895319660429/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((89046222233/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6947381885373761/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((242594459165172805130409/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((89046222233/1000000000000) : ℚ) = (0.089046222233 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((242594459165172805130409/500000000000000000000000) : ℝ) ∧ ((243194195315895319660429/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
      ((243194195315895319660429/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89046222233/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6947381885373761/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((242594459165172805130409/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((89046222233/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨21,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy21 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨21,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨21,by decide⟩).lower) ≤ (scalarRow12222.table ⟨21,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((242594459165172805130409/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((242594459165172805130409/500000000000000000000000) : ℝ)) ≤ ((6947381885373761/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy21 (n := 12222) (by norm_num)
    (q := 1 - ((242594459165172805130409/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell22 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨22,by decide⟩).lower ∧ (scalarRow12222.table ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (scalarRow12222.table ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((486388390631790639320857/1000000000000000000000000) : ℝ) ∧ ((487587862933235668380897/1000000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((487587862933235668380897/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89046222233/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1735403307777761/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((486388390631790639320857/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((89046222233/1000000000000) : ℝ) = (0.089046222233 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((486388390631790639320857/1000000000000000000000000) : ℚ) ∧ ((487587862933235668380897/1000000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((487587862933235668380897/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((89046222233/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1735403307777761/2500000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((486388390631790639320857/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((89046222233/1000000000000) : ℚ) = (0.089046222233 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((486388390631790639320857/1000000000000000000000000) : ℝ) ∧ ((487587862933235668380897/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
      ((487587862933235668380897/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89046222233/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1735403307777761/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((486388390631790639320857/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((89046222233/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨22,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy22 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨22,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨22,by decide⟩).lower) ≤ (scalarRow12222.table ⟨22,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((486388390631790639320857/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((486388390631790639320857/1000000000000000000000000) : ℝ)) ≤ ((1735403307777761/2500000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy22 (n := 12222) (by norm_num)
    (q := 1 - ((486388390631790639320857/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell23 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨23,by decide⟩).lower ∧ (scalarRow12222.table ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (scalarRow12222.table ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((15237120716663614636903/31250000000000000000000) : ℝ) ∧ ((61098416904335087180117/125000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((61098416904335087180117/125000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89046222233/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((346792552015643/500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((15237120716663614636903/31250000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((89046222233/1000000000000) : ℝ) = (0.089046222233 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((15237120716663614636903/31250000000000000000000) : ℚ) ∧ ((61098416904335087180117/125000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((61098416904335087180117/125000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((89046222233/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((346792552015643/500000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((15237120716663614636903/31250000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((89046222233/1000000000000) : ℚ) = (0.089046222233 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((15237120716663614636903/31250000000000000000000) : ℝ) ∧ ((61098416904335087180117/125000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
      ((61098416904335087180117/125000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89046222233/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((346792552015643/500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((15237120716663614636903/31250000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((89046222233/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨23,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy23 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨23,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨23,by decide⟩).lower) ≤ (scalarRow12222.table ⟨23,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((15237120716663614636903/31250000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((15237120716663614636903/31250000000000000000000) : ℝ)) ≤ ((346792552015643/500000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy23 (n := 12222) (by norm_num)
    (q := 1 - ((15237120716663614636903/31250000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell24 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨24,by decide⟩).lower ∧ (scalarRow12222.table ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (scalarRow12222.table ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((97757467046936139488187/200000000000000000000000) : ℝ) ∧ ((19599472301445029060039/40000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((19599472301445029060039/40000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((90030997301/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6930095302393621/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((97757467046936139488187/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((90030997301/1000000000000) : ℝ) = (0.090030997301 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((97757467046936139488187/200000000000000000000000) : ℚ) ∧ ((19599472301445029060039/40000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((19599472301445029060039/40000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((90030997301/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6930095302393621/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((97757467046936139488187/200000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((90030997301/1000000000000) : ℚ) = (0.090030997301 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((97757467046936139488187/200000000000000000000000) : ℝ) ∧ ((19599472301445029060039/40000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
      ((19599472301445029060039/40000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((90030997301/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6930095302393621/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((97757467046936139488187/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((90030997301/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨24,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy24 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨24,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨24,by decide⟩).lower) ≤ (scalarRow12222.table ⟨24,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((97757467046936139488187/200000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((97757467046936139488187/200000000000000000000000) : ℝ)) ≤ ((6930095302393621/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy24 (n := 12222) (by norm_num)
    (q := 1 - ((97757467046936139488187/200000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell25 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨25,by decide⟩).lower ∧ (scalarRow12222.table ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (scalarRow12222.table ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((244993403768062863250487/500000000000000000000000) : ℝ) ∧ ((245593139918785377780507/500000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((245593139918785377780507/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((90030997301/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6924346006808927/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((244993403768062863250487/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((90030997301/1000000000000) : ℝ) = (0.090030997301 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((244993403768062863250487/500000000000000000000000) : ℚ) ∧ ((245593139918785377780507/500000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((245593139918785377780507/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((90030997301/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6924346006808927/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((244993403768062863250487/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((90030997301/1000000000000) : ℚ) = (0.090030997301 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((244993403768062863250487/500000000000000000000000) : ℝ) ∧ ((245593139918785377780507/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
      ((245593139918785377780507/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((90030997301/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6924346006808927/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((244993403768062863250487/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((90030997301/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨25,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy25 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨25,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨25,by decide⟩).lower) ≤ (scalarRow12222.table ⟨25,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((244993403768062863250487/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((244993403768062863250487/500000000000000000000000) : ℝ)) ≤ ((6924346006808927/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy25 (n := 12222) (by norm_num)
    (q := 1 - ((244993403768062863250487/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell26 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨26,by decide⟩).lower ∧ (scalarRow12222.table ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (scalarRow12222.table ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((491186279837570755561013/1000000000000000000000000) : ℝ) ∧ ((492385752139015784621053/1000000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((492385752139015784621053/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((90030997301/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1383720628611063/2000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((491186279837570755561013/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((90030997301/1000000000000) : ℝ) = (0.090030997301 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((491186279837570755561013/1000000000000000000000000) : ℚ) ∧ ((492385752139015784621053/1000000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((492385752139015784621053/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((90030997301/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1383720628611063/2000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((491186279837570755561013/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((90030997301/1000000000000) : ℚ) = (0.090030997301 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((491186279837570755561013/1000000000000000000000000) : ℝ) ∧ ((492385752139015784621053/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
      ((492385752139015784621053/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((90030997301/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1383720628611063/2000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((491186279837570755561013/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((90030997301/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨26,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy26 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨26,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨26,by decide⟩).lower) ≤ (scalarRow12222.table ⟨26,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((491186279837570755561013/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((491186279837570755561013/1000000000000000000000000) : ℝ)) ≤ ((1383720628611063/2000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy26 (n := 12222) (by norm_num)
    (q := 1 - ((491186279837570755561013/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell27 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨27,by decide⟩).lower ∧ (scalarRow12222.table ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (scalarRow12222.table ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((123096438034753946155263/250000000000000000000000) : ℝ) ∧ ((123396306110115203420273/250000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((123396306110115203420273/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((90030997301/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3456433350335001/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((123096438034753946155263/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((90030997301/1000000000000) : ℝ) = (0.090030997301 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((123096438034753946155263/250000000000000000000000) : ℚ) ∧ ((123396306110115203420273/250000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((123396306110115203420273/250000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((90030997301/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3456433350335001/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((123096438034753946155263/250000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((90030997301/1000000000000) : ℚ) = (0.090030997301 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((123096438034753946155263/250000000000000000000000) : ℝ) ∧ ((123396306110115203420273/250000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
      ((123396306110115203420273/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((90030997301/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3456433350335001/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((123096438034753946155263/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((90030997301/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨27,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy27 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨27,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨27,by decide⟩).lower) ≤ (scalarRow12222.table ⟨27,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((123096438034753946155263/250000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((123096438034753946155263/250000000000000000000000) : ℝ)) ≤ ((3456433350335001/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy27 (n := 12222) (by norm_num)
    (q := 1 - ((123096438034753946155263/250000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell28 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨28,by decide⟩).lower ∧ (scalarRow12222.table ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (scalarRow12222.table ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((493585224440460813681091/1000000000000000000000000) : ℝ) ∧ ((494784696741905842741131/1000000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((494784696741905842741131/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((90030997301/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1726784167307661/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((493585224440460813681091/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((90030997301/1000000000000) : ℝ) = (0.090030997301 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((493585224440460813681091/1000000000000000000000000) : ℚ) ∧ ((494784696741905842741131/1000000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((494784696741905842741131/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((90030997301/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1726784167307661/2500000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((493585224440460813681091/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((90030997301/1000000000000) : ℚ) = (0.090030997301 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((493585224440460813681091/1000000000000000000000000) : ℝ) ∧ ((494784696741905842741131/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
      ((494784696741905842741131/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((90030997301/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1726784167307661/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((493585224440460813681091/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((90030997301/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨28,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy28 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨28,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨28,by decide⟩).lower) ≤ (scalarRow12222.table ⟨28,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((493585224440460813681091/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((493585224440460813681091/1000000000000000000000000) : ℝ)) ≤ ((1726784167307661/2500000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy28 (n := 12222) (by norm_num)
    (q := 1 - ((493585224440460813681091/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell29 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨29,by decide⟩).lower ∧ (scalarRow12222.table ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (scalarRow12222.table ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((49478469674190584274113/100000000000000000000000) : ℝ) ∧ ((49598416904335087180117/100000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((49598416904335087180117/100000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((90030997301/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6901413038355081/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((49478469674190584274113/100000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((90030997301/1000000000000) : ℝ) = (0.090030997301 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((49478469674190584274113/100000000000000000000000) : ℚ) ∧ ((49598416904335087180117/100000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((49598416904335087180117/100000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((90030997301/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6901413038355081/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((49478469674190584274113/100000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((90030997301/1000000000000) : ℚ) = (0.090030997301 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((49478469674190584274113/100000000000000000000000) : ℝ) ∧ ((49598416904335087180117/100000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
      ((49598416904335087180117/100000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((90030997301/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6901413038355081/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((49478469674190584274113/100000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((90030997301/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨29,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy29 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨29,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨29,by decide⟩).lower) ≤ (scalarRow12222.table ⟨29,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((49478469674190584274113/100000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((49478469674190584274113/100000000000000000000000) : ℝ)) ≤ ((6901413038355081/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy29 (n := 12222) (by norm_num)
    (q := 1 - ((49478469674190584274113/100000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell30 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨30,by decide⟩).lower ∧ (scalarRow12222.table ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (scalarRow12222.table ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((495984169043350871801169/1000000000000000000000000) : ℝ) ∧ ((497183641344795900861209/1000000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((497183641344795900861209/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45512384207/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3447847898850551/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((495984169043350871801169/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((45512384207/500000000000) : ℝ) = (0.091024768414 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((495984169043350871801169/1000000000000000000000000) : ℚ) ∧ ((497183641344795900861209/1000000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((497183641344795900861209/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((45512384207/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3447847898850551/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((495984169043350871801169/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((45512384207/500000000000) : ℚ) = (0.091024768414 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((495984169043350871801169/1000000000000000000000000) : ℝ) ∧ ((497183641344795900861209/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
      ((497183641344795900861209/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45512384207/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3447847898850551/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((495984169043350871801169/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((45512384207/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨30,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy30 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨30,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨30,by decide⟩).lower) ≤ (scalarRow12222.table ⟨30,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((495984169043350871801169/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((495984169043350871801169/1000000000000000000000000) : ℝ)) ≤ ((3447847898850551/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy30 (n := 12222) (by norm_num)
    (q := 1 - ((495984169043350871801169/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell31 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨31,by decide⟩).lower ∧ (scalarRow12222.table ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (scalarRow12222.table ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((62147955168099487607651/125000000000000000000000) : ℝ) ∧ ((15574472301445029060039/31250000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((15574472301445029060039/31250000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45512384207/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3444992468483097/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((62147955168099487607651/125000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((45512384207/500000000000) : ℝ) = (0.091024768414 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((62147955168099487607651/125000000000000000000000) : ℚ) ∧ ((15574472301445029060039/31250000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((15574472301445029060039/31250000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((45512384207/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3444992468483097/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((62147955168099487607651/125000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((45512384207/500000000000) : ℚ) = (0.091024768414 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((62147955168099487607651/125000000000000000000000) : ℝ) ∧ ((15574472301445029060039/31250000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
      ((15574472301445029060039/31250000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45512384207/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3444992468483097/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((62147955168099487607651/125000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((45512384207/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨31,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy31 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨31,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨31,by decide⟩).lower) ≤ (scalarRow12222.table ⟨31,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((62147955168099487607651/125000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((62147955168099487607651/125000000000000000000000) : ℝ)) ≤ ((3444992468483097/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy31 (n := 12222) (by norm_num)
    (q := 1 - ((62147955168099487607651/125000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell32 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨32,by decide⟩).lower ∧ (scalarRow12222.table ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (scalarRow12222.table ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((498383113646240929921247/1000000000000000000000000) : ℝ) ∧ ((499582585947685958981287/1000000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((499582585947685958981287/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45512384207/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6884280445887309/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((498383113646240929921247/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((45512384207/500000000000) : ℝ) = (0.091024768414 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((498383113646240929921247/1000000000000000000000000) : ℚ) ∧ ((499582585947685958981287/1000000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((499582585947685958981287/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((45512384207/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6884280445887309/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((498383113646240929921247/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((45512384207/500000000000) : ℚ) = (0.091024768414 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((498383113646240929921247/1000000000000000000000000) : ℝ) ∧ ((499582585947685958981287/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
      ((499582585947685958981287/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45512384207/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6884280445887309/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((498383113646240929921247/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((45512384207/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨32,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy32 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨32,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨32,by decide⟩).lower) ≤ (scalarRow12222.table ⟨32,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((498383113646240929921247/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((498383113646240929921247/1000000000000000000000000) : ℝ)) ≤ ((6884280445887309/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy32 (n := 12222) (by norm_num)
    (q := 1 - ((498383113646240929921247/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell33 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨33,by decide⟩).lower ∧ (scalarRow12222.table ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (scalarRow12222.table ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((249791292973842979490643/500000000000000000000000) : ℝ) ∧ ((250391029124565494020663/500000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((250391029124565494020663/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45512384207/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6878582314240619/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((249791292973842979490643/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((45512384207/500000000000) : ℝ) = (0.091024768414 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((249791292973842979490643/500000000000000000000000) : ℚ) ∧ ((250391029124565494020663/500000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((250391029124565494020663/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((45512384207/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6878582314240619/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((249791292973842979490643/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((45512384207/500000000000) : ℚ) = (0.091024768414 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((249791292973842979490643/500000000000000000000000) : ℝ) ∧ ((250391029124565494020663/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
      ((250391029124565494020663/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45512384207/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6878582314240619/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((249791292973842979490643/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((45512384207/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨33,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy33 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨33,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨33,by decide⟩).lower) ≤ (scalarRow12222.table ⟨33,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((249791292973842979490643/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((249791292973842979490643/500000000000000000000000) : ℝ)) ≤ ((6878582314240619/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy33 (n := 12222) (by norm_num)
    (q := 1 - ((249791292973842979490643/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell34 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨34,by decide⟩).lower ∧ (scalarRow12222.table ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (scalarRow12222.table ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((20031282329965239521653/40000000000000000000000) : ℝ) ∧ ((100396306110115203420273/200000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((100396306110115203420273/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45512384207/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((859111316480161/1250000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((20031282329965239521653/40000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((45512384207/500000000000) : ℝ) = (0.091024768414 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((20031282329965239521653/40000000000000000000000) : ℚ) ∧ ((100396306110115203420273/200000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((100396306110115203420273/200000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((45512384207/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((859111316480161/1250000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((20031282329965239521653/40000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((45512384207/500000000000) : ℚ) = (0.091024768414 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((20031282329965239521653/40000000000000000000000) : ℝ) ∧ ((100396306110115203420273/200000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
      ((100396306110115203420273/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45512384207/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((859111316480161/1250000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((20031282329965239521653/40000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((45512384207/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨34,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy34 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨34,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨34,by decide⟩).lower) ≤ (scalarRow12222.table ⟨34,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((20031282329965239521653/40000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((20031282329965239521653/40000000000000000000000) : ℝ)) ≤ ((859111316480161/1250000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy34 (n := 12222) (by norm_num)
    (q := 1 - ((20031282329965239521653/40000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell35 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨35,by decide⟩).lower ∧ (scalarRow12222.table ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (scalarRow12222.table ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((125495382637644004275341/250000000000000000000000) : ℝ) ∧ ((125795250713005261540351/250000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((125795250713005261540351/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45512384207/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((686720508854323/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((125495382637644004275341/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((45512384207/500000000000) : ℝ) = (0.091024768414 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((125495382637644004275341/250000000000000000000000) : ℚ) ∧ ((125795250713005261540351/250000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((125795250713005261540351/250000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((45512384207/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((686720508854323/1000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((125495382637644004275341/250000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((45512384207/500000000000) : ℚ) = (0.091024768414 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((125495382637644004275341/250000000000000000000000) : ℝ) ∧ ((125795250713005261540351/250000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
      ((125795250713005261540351/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((45512384207/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((686720508854323/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((125495382637644004275341/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((45512384207/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨35,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy35 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨35,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨35,by decide⟩).lower) ≤ (scalarRow12222.table ⟨35,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((125495382637644004275341/250000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((125495382637644004275341/250000000000000000000000) : ℝ)) ≤ ((686720508854323/1000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy35 (n := 12222) (by norm_num)
    (q := 1 - ((125495382637644004275341/250000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell36 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨36,by decide⟩).lower ∧ (scalarRow12222.table ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (scalarRow12222.table ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((503181002852021046161403/1000000000000000000000000) : ℝ) ∧ ((504380475153466075221443/1000000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((504380475153466075221443/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23007790407/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6861525974238881/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((503181002852021046161403/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((23007790407/250000000000) : ℝ) = (0.092031161628 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((503181002852021046161403/1000000000000000000000000) : ℚ) ∧ ((504380475153466075221443/1000000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((504380475153466075221443/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((23007790407/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6861525974238881/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((503181002852021046161403/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((23007790407/250000000000) : ℚ) = (0.092031161628 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((503181002852021046161403/1000000000000000000000000) : ℝ) ∧ ((504380475153466075221443/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
      ((504380475153466075221443/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23007790407/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6861525974238881/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((503181002852021046161403/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((23007790407/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨36,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy36 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨36,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨36,by decide⟩).lower) ≤ (scalarRow12222.table ⟨36,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((503181002852021046161403/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((503181002852021046161403/1000000000000000000000000) : ℝ)) ≤ ((6861525974238881/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy36 (n := 12222) (by norm_num)
    (q := 1 - ((503181002852021046161403/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell37 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨37,by decide⟩).lower ∧ (scalarRow12222.table ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (scalarRow12222.table ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((252190237576733037610721/500000000000000000000000) : ℝ) ∧ ((252789973727455552140741/500000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((252789973727455552140741/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23007790407/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((685585317885897/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((252190237576733037610721/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((23007790407/250000000000) : ℝ) = (0.092031161628 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((252190237576733037610721/500000000000000000000000) : ℚ) ∧ ((252789973727455552140741/500000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((252789973727455552140741/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((23007790407/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((685585317885897/1000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((252190237576733037610721/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((23007790407/250000000000) : ℚ) = (0.092031161628 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((252190237576733037610721/500000000000000000000000) : ℝ) ∧ ((252789973727455552140741/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
      ((252789973727455552140741/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23007790407/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((685585317885897/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((252190237576733037610721/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((23007790407/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨37,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy37 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨37,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨37,by decide⟩).lower) ≤ (scalarRow12222.table ⟨37,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((252190237576733037610721/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((252190237576733037610721/500000000000000000000000) : ℝ)) ≤ ((685585317885897/1000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy37 (n := 12222) (by norm_num)
    (q := 1 - ((252190237576733037610721/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell38 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨38,by decide⟩).lower ∧ (scalarRow12222.table ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (scalarRow12222.table ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((505579947454911104281481/1000000000000000000000000) : ℝ) ∧ ((506779419756356133341521/1000000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((506779419756356133341521/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23007790407/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6850186692372289/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((505579947454911104281481/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((23007790407/250000000000) : ℝ) = (0.092031161628 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((505579947454911104281481/1000000000000000000000000) : ℚ) ∧ ((506779419756356133341521/1000000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((506779419756356133341521/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((23007790407/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6850186692372289/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((505579947454911104281481/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((23007790407/250000000000) : ℚ) = (0.092031161628 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((505579947454911104281481/1000000000000000000000000) : ℝ) ∧ ((506779419756356133341521/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
      ((506779419756356133341521/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23007790407/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6850186692372289/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((505579947454911104281481/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((23007790407/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨38,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy38 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨38,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨38,by decide⟩).lower) ≤ (scalarRow12222.table ⟨38,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((505579947454911104281481/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((505579947454911104281481/1000000000000000000000000) : ℝ)) ≤ ((6850186692372289/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy38 (n := 12222) (by norm_num)
    (q := 1 - ((505579947454911104281481/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell39 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨39,by decide⟩).lower ∧ (scalarRow12222.table ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (scalarRow12222.table ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((6334742746954451666769/12500000000000000000000) : ℝ) ∧ ((12699472301445029060039/25000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((12699472301445029060039/25000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23007790407/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((855565813098183/1250000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((6334742746954451666769/12500000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((23007790407/250000000000) : ℝ) = (0.092031161628 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((6334742746954451666769/12500000000000000000000) : ℚ) ∧ ((12699472301445029060039/25000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((12699472301445029060039/25000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((23007790407/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((855565813098183/1250000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((6334742746954451666769/12500000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((23007790407/250000000000) : ℚ) = (0.092031161628 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((6334742746954451666769/12500000000000000000000) : ℝ) ∧ ((12699472301445029060039/25000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
      ((12699472301445029060039/25000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23007790407/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((855565813098183/1250000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((6334742746954451666769/12500000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((23007790407/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨39,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy39 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨39,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨39,by decide⟩).lower) ≤ (scalarRow12222.table ⟨39,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((6334742746954451666769/12500000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((6334742746954451666769/12500000000000000000000) : ℝ)) ≤ ((855565813098183/1250000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy39 (n := 12222) (by norm_num)
    (q := 1 - ((6334742746954451666769/12500000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell40 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨40,by decide⟩).lower ∧ (scalarRow12222.table ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (scalarRow12222.table ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((507978892057801162401559/1000000000000000000000000) : ℝ) ∧ ((509178364359246191461599/1000000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((509178364359246191461599/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23007790407/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3419436303071369/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((507978892057801162401559/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((23007790407/250000000000) : ℝ) = (0.092031161628 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((507978892057801162401559/1000000000000000000000000) : ℚ) ∧ ((509178364359246191461599/1000000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((509178364359246191461599/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((23007790407/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3419436303071369/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((507978892057801162401559/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((23007790407/250000000000) : ℚ) = (0.092031161628 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((507978892057801162401559/1000000000000000000000000) : ℝ) ∧ ((509178364359246191461599/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
      ((509178364359246191461599/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23007790407/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3419436303071369/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((507978892057801162401559/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((23007790407/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨40,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy40 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨40,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨40,by decide⟩).lower) ≤ (scalarRow12222.table ⟨40,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((507978892057801162401559/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((507978892057801162401559/1000000000000000000000000) : ℝ)) ≤ ((3419436303071369/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy40 (n := 12222) (by norm_num)
    (q := 1 - ((507978892057801162401559/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell41 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨41,by decide⟩).lower ∧ (scalarRow12222.table ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (scalarRow12222.table ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((254589182179623095730799/500000000000000000000000) : ℝ) ∧ ((255188918330345610260819/500000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((255188918330345610260819/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23007790407/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6833224986525741/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((254589182179623095730799/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((23007790407/250000000000) : ℝ) = (0.092031161628 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((254589182179623095730799/500000000000000000000000) : ℚ) ∧ ((255188918330345610260819/500000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((255188918330345610260819/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((23007790407/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6833224986525741/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((254589182179623095730799/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((23007790407/250000000000) : ℚ) = (0.092031161628 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((254589182179623095730799/500000000000000000000000) : ℝ) ∧ ((255188918330345610260819/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
      ((255188918330345610260819/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((23007790407/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6833224986525741/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((254589182179623095730799/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((23007790407/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨41,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy41 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨41,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨41,by decide⟩).lower) ≤ (scalarRow12222.table ⟨41,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((254589182179623095730799/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((254589182179623095730799/500000000000000000000000) : ℝ)) ≤ ((6833224986525741/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy41 (n := 12222) (by norm_num)
    (q := 1 - ((254589182179623095730799/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell42 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨42,by decide⟩).lower ∧ (scalarRow12222.table ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (scalarRow12222.table ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((510377836660691220521637/1000000000000000000000000) : ℝ) ∧ ((511577308962136249581677/1000000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((511577308962136249581677/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93054434941/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3413791818026637/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((510377836660691220521637/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((93054434941/1000000000000) : ℝ) = (0.093054434941 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((510377836660691220521637/1000000000000000000000000) : ℚ) ∧ ((511577308962136249581677/1000000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((511577308962136249581677/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((93054434941/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3413791818026637/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((510377836660691220521637/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((93054434941/1000000000000) : ℚ) = (0.093054434941 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((510377836660691220521637/1000000000000000000000000) : ℝ) ∧ ((511577308962136249581677/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
      ((511577308962136249581677/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93054434941/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3413791818026637/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((510377836660691220521637/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((93054434941/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨42,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy42 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨42,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨42,by decide⟩).lower) ≤ (scalarRow12222.table ⟨42,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((510377836660691220521637/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((510377836660691220521637/1000000000000000000000000) : ℝ)) ≤ ((3413791818026637/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy42 (n := 12222) (by norm_num)
    (q := 1 - ((510377836660691220521637/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell43 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨43,by decide⟩).lower ∧ (scalarRow12222.table ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (scalarRow12222.table ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((127894327240534062395419/250000000000000000000000) : ℝ) ∧ ((128194195315895319660429/250000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((128194195315895319660429/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93054434941/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((106592946013767/156250000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((127894327240534062395419/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((93054434941/1000000000000) : ℝ) = (0.093054434941 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((127894327240534062395419/250000000000000000000000) : ℚ) ∧ ((128194195315895319660429/250000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((128194195315895319660429/250000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((93054434941/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((106592946013767/156250000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((127894327240534062395419/250000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((93054434941/1000000000000) : ℚ) = (0.093054434941 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((127894327240534062395419/250000000000000000000000) : ℝ) ∧ ((128194195315895319660429/250000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
      ((128194195315895319660429/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93054434941/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((106592946013767/156250000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((127894327240534062395419/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((93054434941/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨43,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy43 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨43,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨43,by decide⟩).lower) ≤ (scalarRow12222.table ⟨43,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((127894327240534062395419/250000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((127894327240534062395419/250000000000000000000000) : ℝ)) ≤ ((106592946013767/156250000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy43 (n := 12222) (by norm_num)
    (q := 1 - ((127894327240534062395419/250000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell44 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨44,by decide⟩).lower ∧ (scalarRow12222.table ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (scalarRow12222.table ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((102555356252716255728343/200000000000000000000000) : ℝ) ∧ ((102795250713005261540351/200000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((102795250713005261540351/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93054434941/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((681631970320167/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((102555356252716255728343/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((93054434941/1000000000000) : ℝ) = (0.093054434941 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((102555356252716255728343/200000000000000000000000) : ℚ) ∧ ((102795250713005261540351/200000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((102795250713005261540351/200000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((93054434941/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((681631970320167/1000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((102555356252716255728343/200000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((93054434941/1000000000000) : ℚ) = (0.093054434941 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((102555356252716255728343/200000000000000000000000) : ℝ) ∧ ((102795250713005261540351/200000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
      ((102795250713005261540351/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93054434941/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((681631970320167/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((102555356252716255728343/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((93054434941/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨44,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy44 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨44,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨44,by decide⟩).lower) ≤ (scalarRow12222.table ⟨44,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((102555356252716255728343/200000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((102555356252716255728343/200000000000000000000000) : ℝ)) ≤ ((681631970320167/1000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy44 (n := 12222) (by norm_num)
    (q := 1 - ((102555356252716255728343/200000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell45 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨45,by decide⟩).lower ∧ (scalarRow12222.table ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (scalarRow12222.table ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((256988126782513153850877/500000000000000000000000) : ℝ) ∧ ((257587862933235668380897/500000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((257587862933235668380897/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93054434941/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6810697101244023/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((256988126782513153850877/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((93054434941/1000000000000) : ℝ) = (0.093054434941 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((256988126782513153850877/500000000000000000000000) : ℚ) ∧ ((257587862933235668380897/500000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((257587862933235668380897/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((93054434941/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6810697101244023/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((256988126782513153850877/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((93054434941/1000000000000) : ℚ) = (0.093054434941 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((256988126782513153850877/500000000000000000000000) : ℝ) ∧ ((257587862933235668380897/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
      ((257587862933235668380897/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93054434941/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6810697101244023/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((256988126782513153850877/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((93054434941/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨45,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy45 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨45,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨45,by decide⟩).lower) ≤ (scalarRow12222.table ⟨45,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((256988126782513153850877/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((256988126782513153850877/500000000000000000000000) : ℝ)) ≤ ((6810697101244023/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy45 (n := 12222) (by norm_num)
    (q := 1 - ((256988126782513153850877/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell46 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨46,by decide⟩).lower ∧ (scalarRow12222.table ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (scalarRow12222.table ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((515175725866471336761793/1000000000000000000000000) : ℝ) ∧ ((516375198167916365821833/1000000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((516375198167916365821833/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93054434941/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3402540364636729/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((515175725866471336761793/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((93054434941/1000000000000) : ℝ) = (0.093054434941 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((515175725866471336761793/1000000000000000000000000) : ℚ) ∧ ((516375198167916365821833/1000000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((516375198167916365821833/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((93054434941/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3402540364636729/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((515175725866471336761793/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((93054434941/1000000000000) : ℚ) = (0.093054434941 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((515175725866471336761793/1000000000000000000000000) : ℝ) ∧ ((516375198167916365821833/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
      ((516375198167916365821833/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93054434941/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3402540364636729/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((515175725866471336761793/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((93054434941/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨46,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy46 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨46,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨46,by decide⟩).lower) ≤ (scalarRow12222.table ⟨46,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((515175725866471336761793/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((515175725866471336761793/1000000000000000000000000) : ℝ)) ≤ ((3402540364636729/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy46 (n := 12222) (by norm_num)
    (q := 1 - ((515175725866471336761793/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell47 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨47,by decide⟩).lower ∧ (scalarRow12222.table ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (scalarRow12222.table ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((64546899770989545727729/125000000000000000000000) : ℝ) ∧ ((32348416904335087180117/62500000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((32348416904335087180117/62500000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93054434941/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6799470577591379/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((64546899770989545727729/125000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((93054434941/1000000000000) : ℝ) = (0.093054434941 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((64546899770989545727729/125000000000000000000000) : ℚ) ∧ ((32348416904335087180117/62500000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((32348416904335087180117/62500000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((93054434941/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6799470577591379/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((64546899770989545727729/125000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((93054434941/1000000000000) : ℚ) = (0.093054434941 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((64546899770989545727729/125000000000000000000000) : ℝ) ∧ ((32348416904335087180117/62500000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
      ((32348416904335087180117/62500000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93054434941/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6799470577591379/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((64546899770989545727729/125000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((93054434941/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨47,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy47 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨47,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨47,by decide⟩).lower) ≤ (scalarRow12222.table ⟨47,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((64546899770989545727729/125000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((64546899770989545727729/125000000000000000000000) : ℝ)) ≤ ((6799470577591379/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy47 (n := 12222) (by norm_num)
    (q := 1 - ((64546899770989545727729/125000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell48 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨48,by decide⟩).lower ∧ (scalarRow12222.table ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (scalarRow12222.table ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((517574670469361394881871/1000000000000000000000000) : ℝ) ∧ ((518774142770806423941911/1000000000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((518774142770806423941911/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((94099555469/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3396933318267537/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((517574670469361394881871/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((94099555469/1000000000000) : ℝ) = (0.094099555469 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((517574670469361394881871/1000000000000000000000000) : ℚ) ∧ ((518774142770806423941911/1000000000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((518774142770806423941911/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((94099555469/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3396933318267537/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((517574670469361394881871/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((94099555469/1000000000000) : ℚ) = (0.094099555469 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((517574670469361394881871/1000000000000000000000000) : ℝ) ∧ ((518774142770806423941911/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
      ((518774142770806423941911/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((94099555469/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3396933318267537/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((517574670469361394881871/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((94099555469/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨48,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy48 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨48,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨48,by decide⟩).lower) ≤ (scalarRow12222.table ⟨48,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((517574670469361394881871/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((517574670469361394881871/1000000000000000000000000) : ℝ)) ≤ ((3396933318267537/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy48 (n := 12222) (by norm_num)
    (q := 1 - ((517574670469361394881871/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell49 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨49,by decide⟩).lower ∧ (scalarRow12222.table ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (scalarRow12222.table ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((51877414277080642394191/100000000000000000000000) : ℝ) ∧ ((10399472301445029060039/20000000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((10399472301445029060039/20000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((94099555469/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((678826889647751/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((51877414277080642394191/100000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((94099555469/1000000000000) : ℝ) = (0.094099555469 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((51877414277080642394191/100000000000000000000000) : ℚ) ∧ ((10399472301445029060039/20000000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((10399472301445029060039/20000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((94099555469/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((678826889647751/1000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((51877414277080642394191/100000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((94099555469/1000000000000) : ℚ) = (0.094099555469 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((51877414277080642394191/100000000000000000000000) : ℝ) ∧ ((10399472301445029060039/20000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
      ((10399472301445029060039/20000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((94099555469/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((678826889647751/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((51877414277080642394191/100000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((94099555469/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨49,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy49 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨49,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨49,by decide⟩).lower) ≤ (scalarRow12222.table ⟨49,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((51877414277080642394191/100000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((51877414277080642394191/100000000000000000000000) : ℝ)) ≤ ((678826889647751/1000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy49 (n := 12222) (by norm_num)
    (q := 1 - ((51877414277080642394191/100000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell50 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨50,by decide⟩).lower ∧ (scalarRow12222.table ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (scalarRow12222.table ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((519973615072251453001949/1000000000000000000000000) : ℝ) ∧ ((521173087373696482061989/1000000000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((521173087373696482061989/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((94099555469/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6782677347827119/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((519973615072251453001949/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((94099555469/1000000000000) : ℝ) = (0.094099555469 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((519973615072251453001949/1000000000000000000000000) : ℚ) ∧ ((521173087373696482061989/1000000000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((521173087373696482061989/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((94099555469/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6782677347827119/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((519973615072251453001949/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((94099555469/1000000000000) : ℚ) = (0.094099555469 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((519973615072251453001949/1000000000000000000000000) : ℝ) ∧ ((521173087373696482061989/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
      ((521173087373696482061989/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((94099555469/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6782677347827119/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((519973615072251453001949/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((94099555469/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨50,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy50 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨50,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨50,by decide⟩).lower) ≤ (scalarRow12222.table ⟨50,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((519973615072251453001949/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((519973615072251453001949/1000000000000000000000000) : ℝ)) ≤ ((6782677347827119/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy50 (n := 12222) (by norm_num)
    (q := 1 - ((519973615072251453001949/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell51 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨51,by decide⟩).lower ∧ (scalarRow12222.table ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (scalarRow12222.table ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((130293271843424120515497/250000000000000000000000) : ℝ) ∧ ((130593139918785377780507/250000000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((130593139918785377780507/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((94099555469/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6777091981027603/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((130293271843424120515497/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((94099555469/1000000000000) : ℝ) = (0.094099555469 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((130293271843424120515497/250000000000000000000000) : ℚ) ∧ ((130593139918785377780507/250000000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((130593139918785377780507/250000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((94099555469/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6777091981027603/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((130293271843424120515497/250000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((94099555469/1000000000000) : ℚ) = (0.094099555469 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((130293271843424120515497/250000000000000000000000) : ℝ) ∧ ((130593139918785377780507/250000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
      ((130593139918785377780507/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((94099555469/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6777091981027603/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((130293271843424120515497/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((94099555469/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨51,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy51 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨51,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨51,by decide⟩).lower) ≤ (scalarRow12222.table ⟨51,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((130293271843424120515497/250000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((130293271843424120515497/250000000000000000000000) : ℝ)) ≤ ((6777091981027603/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy51 (n := 12222) (by norm_num)
    (q := 1 - ((130293271843424120515497/250000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell52 :
    (0.46 : ℝ) ≤ (scalarRow12222.table ⟨52,by decide⟩).lower ∧ (scalarRow12222.table ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (scalarRow12222.table ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((522372559675141511122027/1000000000000000000000000) : ℝ) ∧ ((523572031976586540182067/1000000000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((523572031976586540182067/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((94099555469/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1692878196639431/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((522372559675141511122027/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((94099555469/1000000000000) : ℝ) = (0.094099555469 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((522372559675141511122027/1000000000000000000000000) : ℚ) ∧ ((523572031976586540182067/1000000000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((523572031976586540182067/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((94099555469/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1692878196639431/2500000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((522372559675141511122027/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((94099555469/1000000000000) : ℚ) = (0.094099555469 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((522372559675141511122027/1000000000000000000000000) : ℝ) ∧ ((523572031976586540182067/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
      ((523572031976586540182067/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((94099555469/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1692878196639431/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((522372559675141511122027/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((94099555469/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨52,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy52 :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table ⟨52,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table ⟨52,by decide⟩).lower) ≤ (scalarRow12222.table ⟨52,by decide⟩).energy := by
  change energyRatio 12222 (gMinus 12222) (1 - ((522372559675141511122027/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - ((522372559675141511122027/1000000000000000000000000) : ℝ)) ≤ ((1692878196639431/2500000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy52 (n := 12222) (by norm_num)
    (q := 1 - ((522372559675141511122027/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (scalarRow12222.table i).lower ∧ (scalarRow12222.table i).upper ≤ groupTheta (centreGroup i) ∧
    (scalarRow12222.table i).upper ≤ (0.532 : ℝ) ∧ (scalarRow12222.table i).centre ≤ (0.1 : ℝ) ∧ (scalarRow12222.table i).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12222.table i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12222.table i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨2,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨3,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨4,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨5,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨6,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨7,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨8,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨9,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨10,h⟩ => exact sourceCell10
  | ⟨11,h⟩ => exact sourceCell11
  | ⟨12,h⟩ => exact sourceCell12
  | ⟨13,h⟩ => exact sourceCell13
  | ⟨14,h⟩ => exact sourceCell14
  | ⟨15,h⟩ => exact sourceCell15
  | ⟨16,h⟩ => exact sourceCell16
  | ⟨17,h⟩ => exact sourceCell17
  | ⟨18,h⟩ => exact sourceCell18
  | ⟨19,h⟩ => exact sourceCell19
  | ⟨20,h⟩ => exact sourceCell20
  | ⟨21,h⟩ => exact sourceCell21
  | ⟨22,h⟩ => exact sourceCell22
  | ⟨23,h⟩ => exact sourceCell23
  | ⟨24,h⟩ => exact sourceCell24
  | ⟨25,h⟩ => exact sourceCell25
  | ⟨26,h⟩ => exact sourceCell26
  | ⟨27,h⟩ => exact sourceCell27
  | ⟨28,h⟩ => exact sourceCell28
  | ⟨29,h⟩ => exact sourceCell29
  | ⟨30,h⟩ => exact sourceCell30
  | ⟨31,h⟩ => exact sourceCell31
  | ⟨32,h⟩ => exact sourceCell32
  | ⟨33,h⟩ => exact sourceCell33
  | ⟨34,h⟩ => exact sourceCell34
  | ⟨35,h⟩ => exact sourceCell35
  | ⟨36,h⟩ => exact sourceCell36
  | ⟨37,h⟩ => exact sourceCell37
  | ⟨38,h⟩ => exact sourceCell38
  | ⟨39,h⟩ => exact sourceCell39
  | ⟨40,h⟩ => exact sourceCell40
  | ⟨41,h⟩ => exact sourceCell41
  | ⟨42,h⟩ => exact sourceCell42
  | ⟨43,h⟩ => exact sourceCell43
  | ⟨44,h⟩ => exact sourceCell44
  | ⟨45,h⟩ => exact sourceCell45
  | ⟨46,h⟩ => exact sourceCell46
  | ⟨47,h⟩ => exact sourceCell47
  | ⟨48,h⟩ => exact sourceCell48
  | ⟨49,h⟩ => exact sourceCell49
  | ⟨50,h⟩ => exact sourceCell50
  | ⟨51,h⟩ => exact sourceCell51
  | ⟨52,h⟩ => exact sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

theorem upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12222 (gMinus 12222) (1 - (scalarRow12222.table i).lower) ≤ 1 ∧
    energyUpper 12222 (gMinus 12222) (BstLean.Part211.gPlus 12222)
      (finiteEnergy 12222 12222 0.011) (1 - (scalarRow12222.table i).lower) ≤ (scalarRow12222.table i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨2,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨3,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨4,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨5,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨6,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨7,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨8,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨9,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨10,h⟩ => exact upperEnergy10
  | ⟨11,h⟩ => exact upperEnergy11
  | ⟨12,h⟩ => exact upperEnergy12
  | ⟨13,h⟩ => exact upperEnergy13
  | ⟨14,h⟩ => exact upperEnergy14
  | ⟨15,h⟩ => exact upperEnergy15
  | ⟨16,h⟩ => exact upperEnergy16
  | ⟨17,h⟩ => exact upperEnergy17
  | ⟨18,h⟩ => exact upperEnergy18
  | ⟨19,h⟩ => exact upperEnergy19
  | ⟨20,h⟩ => exact upperEnergy20
  | ⟨21,h⟩ => exact upperEnergy21
  | ⟨22,h⟩ => exact upperEnergy22
  | ⟨23,h⟩ => exact upperEnergy23
  | ⟨24,h⟩ => exact upperEnergy24
  | ⟨25,h⟩ => exact upperEnergy25
  | ⟨26,h⟩ => exact upperEnergy26
  | ⟨27,h⟩ => exact upperEnergy27
  | ⟨28,h⟩ => exact upperEnergy28
  | ⟨29,h⟩ => exact upperEnergy29
  | ⟨30,h⟩ => exact upperEnergy30
  | ⟨31,h⟩ => exact upperEnergy31
  | ⟨32,h⟩ => exact upperEnergy32
  | ⟨33,h⟩ => exact upperEnergy33
  | ⟨34,h⟩ => exact upperEnergy34
  | ⟨35,h⟩ => exact upperEnergy35
  | ⟨36,h⟩ => exact upperEnergy36
  | ⟨37,h⟩ => exact upperEnergy37
  | ⟨38,h⟩ => exact upperEnergy38
  | ⟨39,h⟩ => exact upperEnergy39
  | ⟨40,h⟩ => exact upperEnergy40
  | ⟨41,h⟩ => exact upperEnergy41
  | ⟨42,h⟩ => exact upperEnergy42
  | ⟨43,h⟩ => exact upperEnergy43
  | ⟨44,h⟩ => exact upperEnergy44
  | ⟨45,h⟩ => exact upperEnergy45
  | ⟨46,h⟩ => exact upperEnergy46
  | ⟨47,h⟩ => exact upperEnergy47
  | ⟨48,h⟩ => exact upperEnergy48
  | ⟨49,h⟩ => exact upperEnergy49
  | ⟨50,h⟩ => exact upperEnergy50
  | ⟨51,h⟩ => exact upperEnergy51
  | ⟨52,h⟩ => exact upperEnergy52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

noncomputable def sourceNumerics12222 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part277.CellSourceNumericsP 12222 (scalarRow12222.table i) scalarRow12222.M scalarRow12222.H scalarRow12222.xi
      1.22 1.12 1.25 0.665 0.47199 0.52358 := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part281.Groups.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := source_cell hi
  have E := upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := BstLean.Part277.centreCertificate_from_momentP (by norm_num)
      (pilot_groupMomentCertificate hg) hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
      (r := (110.553154636129 : ℝ)) (F := (0.008771 : ℝ))
      (by norm_num) (by norm_num) pilot_finite_centre_upper (by norm_num)
      (fun θ hθ => by
        convert (BstLean.Part281.energy_lower_data (by norm_num : 11883 ≤ 12222)
          ⟨hθ.1,hθ.2.trans G.window.2⟩).1 using 1 <;> norm_num)
    energy_allowance := scalarRow12222.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12222]
    centre_nonneg := (scalarRow12222.certificate i).centre_nonneg
    centre_upper := hc
    MP_nonneg := by norm_num
    e0_pos := by norm_num
    operator := by
      intro c τ hτ
      exact (BstLean.Part277.operator_allowance_11883
        (by norm_num : 11883 ≤ 12222) c hτ).trans (by norm_num)
    lower := fun θ hθ => by
      convert (BstLean.Part281.energy_lower_data
        (by norm_num : 11883 ≤ 12222) ⟨hθ.1,hθ.2.trans G.window.2⟩).2 using 1 <;> norm_num
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part281.Dir11883.direction_budget_11883 (by norm_num : 11883 ≤ 12222)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12222])
    source_lower := hl
    source_upper := hu
    source_upper_one := hu532.trans (by norm_num)
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }
end BstLean.Part281.N12222
namespace BstLean.Part281.N12223
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
theorem pilot_wn_upper : wn 12223 ≤ (1.036507462082 : ℝ) := by
  have hr : (110.557677254906 : ℝ) ≤ √(12223 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.557677254906 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : finiteEnergy 12223 12223 (11 / 1000) ≤ (0.008771 : ℝ) := by
  convert BstLean.Part277.finite_centre_11883 (by norm_num : 11883 ≤ 12223) using 1 <;> norm_num
noncomputable def pilotParallelCap : ℝ := BstLean.Part281.scalarRow12223.xi
end BstLean.Part281.N12223

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part281.N12223
open BstLean.Part253
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036507462081 : ℝ) ≤ wn 12223 := by
  have hn : √(12223 : ℝ) ≤ 110.557677254907 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12223 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.557677254907 ≤ 2 / √(12223 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000261886886 : ℝ) ≤ rhoBar 12223 csC ∧
    rhoBar 12223 csC ≤ 0.000261887292 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036507462081 : ℝ) / (1.295212 * 12223) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036507462082 : ℝ) / (1.29521 * 12223) := by gcongr
      _ ≤ (0.000261887292 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12223 csC) ≤ 0.001047617753 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12223 csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part281.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12223 csC) (piBar (rhoBar 12223 csC)) ≤ 0.000200031650 ∧
    cc1 (rhoBar 12223 csC) (piBar (rhoBar 12223 csC)) ≤ 0.000127281391 ∧
    cc2 (rhoBar 12223 csC) ≤ 0.000073887730 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12223 csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12223 csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12223 csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12223 csC * nuR (rhoBar 12223 csC)) ≤ 0.000523791730 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000261887292 : ℝ) * 0.001047617753 := by gcongr
      _ ≤ (0.000523791730 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12223 csC) * nuR (rhoBar 12223 csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001047617753 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12223 csC) * rhoBar 12223 csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000261887292 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000261887292 / 2 + 0.399 * 0.001047617753 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000200031650 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000523791730 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000127281391 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000261887292 / 1.414213562 := by gcongr
      _ ≤ (0.000073887730 : ℝ) := by norm_num

end BstLean.Part281.N12223

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part281.N12223
open BstLean.Part253
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12223 csC) (piBar (rhoBar 12223 csC)) ≤ 1.72795E-7 := by
  have hr0 : 0 ≤ rhoBar 12223 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12223 csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12223 csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12223 csC) (piBar (rhoBar 12223 csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12223 csC) (piBar (rhoBar 12223 csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12223 csC) := by unfold cc2; positivity
  have hc0 := pilot_cc_bounds.1
  have hc1 := pilot_cc_bounds.2.1
  have hc2 := pilot_cc_bounds.2.2
  have hs : √(2 / π) ≤ 0.797885 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ pi_pos).mpr
    linarith [pi_gt_d6]
  unfold QB
  calc
    _ ≤ (0.000200031650 : ℝ) ^ 2 + 0.000127281391 ^ 2 + 3 * 0.000073887730 ^ 2 +
        2 * 0.797885 * 0.000200031650 * 0.000127281391 + 2 * 0.000200031650 * 0.000073887730 +
        4 * 0.797885 * 0.000127281391 * 0.000073887730 := by gcongr
    _ ≤ (1.72795E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12223 csC Θ ≤ 0.002735582674 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12223 csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12223 csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12223 csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12223 csC) (piBar (rhoBar 12223 csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12223 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036507462082 * 1.72795E-7 / (0.000261886886 : ℝ) := by gcongr
    _ ≤ 0.002735582674 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12223 csC Θ ≤ 0.003037328233 + 0.000691237137 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12223 csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12223 csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12223 csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036507462082 : ℝ) * ((2 * Θ * 0.000261887292 +
        (6863 / 10000) * 0.000261887292 * 12223 * 0.001047617753) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003037328233 + 0.000691237137 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09430 : ℝ) ≤ gap 2 (rhoBar 12223 csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997300 : ℝ) ≤ √(1 - 2 * rhoBar 12223 csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12223 0.011 Θ ∧ gammaRatio 12223 0.011 Θ ≤ 0.000090030079 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12223 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036507462082 : ℝ) * 0.525 / ((1 - 0.011) * 12223) := by gcongr
      _ ≤ (0.000090030079 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.05504 : ℝ) ≤ gap 1 (gammaRatio 12223 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.9999535 : ℝ) ≤ √(1 - gammaRatio 12223 0.011 Θ) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.12 ≤ 0.94491119 := by
    calc
      _ ≤ (1 : ℝ) / 1.05830052 := by gcongr
      _ ≤ (0.94491119 : ℝ) := by norm_num
  unfold gap
  rw [one_mul]
  linarith

theorem pilot_bad_upper {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    badAllowance 12223 csC 0.011 1.22 1.12 Θ ≤ 0.001130147379 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12223 csC) 1.22 ≤ 4.5754E-8 := by
    have he : (16.9 : ℝ) ≤ gap 2 (rhoBar 12223 csC) 1.22 ^ 2 / (2 * rhoBar 12223 csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12223 csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part281.Tails.exp_minus_16_9_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12223 0.011 Θ) 1.12 ≤ 5.0566E-8 := by
    have he : (16.8 : ℝ) ≤ gap 1 (gammaRatio 12223 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12223 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12223 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part281.Tails.exp_minus_16_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12223 csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12223 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036507462082 : ℝ) * 12223 *
        (4.5754E-8 / 1.1045361 + 5.0566E-8 / 1.05830052) := by gcongr
    _ ≤ (0.001130147379 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12223 csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004167475612 + 0.003426819811 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part281.N12223

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part281.N12223
open BstLean.Part253
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12223 csC) (piBar (rhoBar 12223 csC)) := by
  have hr0 : 0 ≤ rhoBar 12223 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12223 csC)
  have hv0 : 0 ≤ nuR (rhoBar 12223 csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12223 csC Θ := by
  have hr0 : 0 ≤ rhoBar 12223 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12223 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12223 csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12223 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12223 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12223 csC)
  have hv0 : 0 ≤ nuR (rhoBar 12223 csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12223 csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12223 csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12223 csC 0.011 0.46 Θ ≤ 0.053509817779 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / 12223) ≤ 0.010801941672 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12223 * Θ) ≤ 0.737676363722 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036507462082)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010801941672 + 2 * 0.737676363722 / 12223) := by gcongr
    _ ≤ (0.053509817779 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12223 12 ≤ 0.0016 := by
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar 12223 12 ≤ 0.000749756361 := by
    unfold N12bar
    simp only [Nat.cast_ofNat]
    linarith
  have h10 : 0 ≤ N12bar 12223 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem pilot_radial_centre_bound {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.25 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0016 + T) / 110.557677254906 ≤ R) : xiNr 12223 Θ 1.25 ≤ R := by
  have hs : √((1.25 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hn := pilot_n22_upper
  have hn0 : 0 ≤ N22bar 12223 12 := by unfold N22bar N12bar; positivity
  have hN : (110.557677254906 : ℝ) ≤ √(12223 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold xiNr
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hR
  gcongr
  linarith

theorem pilot_full_formula_bound {Θ S X T R B : ℝ}
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.004167475612 + 0.003426819811 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.25 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0016 + T) / 110.557677254906 ≤ R)
    (hB : (X + 0.053509817779 + R + 0.008771) ^ 2 ≤ B) :
    fullFormula 12223 12223 0.011 1.22 1.12 0.46 Θ S 1.25 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance 12223 csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, (pilot_moment_upper hw hS).trans hXsq⟩
  have hd := pilot_deviation_upper hΘ hw.2
  have hr := pilot_radial_centre_bound hΘ hT hTsq hR
  have hf : finiteEnergy 12223 12223 0.011 ≤ 0.008771 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation 12223 csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar 12223 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr 12223 Θ 1.25 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg 12223 12223 (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

end BstLean.Part281.N12223

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part281.N12223
open BstLean.Part253
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560481155117 : ℝ) ≤ plow 12223 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12223) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053552776013)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001436180904) : eMP 12223 0.011 xi bn ≤ 0.001235780291 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12223 : ℝ) * (1 - 0.011))) ≤ 0.000610931450 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001436180904 / (12223 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000610931450 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000610931450 : ℝ) + 3.141593 * 0.053552776013 / (12223 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001235780291 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053552776013)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001436180904) : PiBarMP 12223 12 0.011 xi bn ≤ 0.164401286230 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12223 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037896977505 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (109.947928584398 : ℝ) ≤ √((12223 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.557677254906 : ℝ) ≤ √(12223 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12223) ≤ 0.126019364812 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037896977505 + 0.053552776013 * 1.772454 / (2 * (109.947928584398 : ℝ))) * (1 + 0.001235780291) +
        8 / (12223 * 110.557677254906) + 0.126019364812 := by gcongr
    _ ≤ (0.164401286230 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053552776013)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001436180904) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284924545083) :
    parallelOracle 12223 0.011 xi bn cd ≤ 0.165434312423 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12223 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12223 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560481155117 : ℝ) ≤ plow 12223 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.557677254906 : ℝ) ≤ √(12223 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.284924545083 : ℝ) / (2 * 0.560481155117 * 110.557677254906)) * 0.164401286230 +
        0.284924545083 ^ 2 / (2 * 0.560481155117 * 110.557677254906) := by gcongr
    _ ≤ (0.165434312423 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053552776013) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001436180904)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.284924545083) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12223 12223 0.011 xi bn cd Θ 1.25 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560481155117 : ℝ) ≤ plow 12223 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.557677254906 : ℝ) ≤ √(12223 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12223 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.25 : ℝ) * Θ) ≤ 0.810092587301 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12223 Θ 1.25 ≤ 0.012083580449 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0016 + 0.810092587301) / 110.557677254906 := by gcongr <;> linarith
      _ ≤ (0.012083580449 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12223 Θ 1.25 := by unfold xiNr; positivity
  have hf : finiteEnergy 12223 12223 0.011 ≤ 0.008771 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12223 12223 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12223 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12223 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12223 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12223 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.165434312423 + 0.012083580449 + (0.008771 : ℝ) *
        (1 + 2 * (0.284924545083 + 0.012083580449) / (0.560481155117 * 110.557677254906))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part281.scalarRow12223]

end BstLean.Part281.N12223

/-! The original eight local profiles supply actual 12223 moment certificates. -/
namespace BstLean.Part281.N12223
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part281.Groups

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : BstLean.Part281.Groups.NeededGroup g) :
    MomentCertificate 12223 0.011 1.22 1.12 0.46 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part281.Groups.group_scalar hg
  exact {
    delta_nonneg := by norm_num
    delta_lt := by norm_num
    k_gt := by norm_num
    k3_gt := by norm_num
    theta_lower := by norm_num
    v_pos := by intro θ hθ; norm_num
    supremum := fun θ hθ => by
      have hθ0 : 0 < θ := lt_of_lt_of_le (by norm_num) hθ.1
      have hθ1 : θ ≤ 1 := hθ.2.trans (G.window.2.trans (by norm_num))
      exact (mul_le_mul_of_nonneg_right (BstLean.Part281.Groups.hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part281.Groups.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : BstLean.Part281.Groups.NeededGroup g) :
    0 ≤ momentAllowance 12223 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g) ∧
    momentAllowance 12223 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g) ≤ 0.053552776013 ∧
    0 ≤ bN 12223 csC (BstLean.Part281.Groups.groupTheta g) ∧ bN 12223 csC (BstLean.Part281.Groups.groupTheta g) ≤ 0.001436180904 := by
  have G := BstLean.Part281.Groups.group_scalar hg
  have hΘ : 0 ≤ BstLean.Part281.Groups.groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : BstLean.Part281.Groups.NeededGroup g) :
    parallelFormula 12223 12223 0.011
      (momentAllowance 12223 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g))
      (bN 12223 csC (BstLean.Part281.Groups.groupTheta g))
      (√(momentAllowance 12223 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g)) +
        sharpDeviation 12223 csC 0.011 0.46 (BstLean.Part281.Groups.groupTheta g)) (BstLean.Part281.Groups.groupTheta g) 1.25 ≤ pilotParallelCap := by
  have G := BstLean.Part281.Groups.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ BstLean.Part281.Groups.groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12223 csC 0.011 0.46 (BstLean.Part281.Groups.groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12223 csC 0.011 1.22 1.12
      (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g)) ≤ 0.231414727304 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : BstLean.Part281.Groups.NeededGroup g) :
    eMP 12223 0.011
      (momentAllowance 12223 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g))
      (bN 12223 csC (BstLean.Part281.Groups.groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part281.N12223
namespace BstLean.Part281.N12223
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.087088306483
  | 2 => 0.088063712267
  | 3 => 0.089042459827
  | 4 => 0.090027119352
  | 5 => 0.091020753412
  | 6 => 0.092026983826
  | 7 => 0.093050063729
  | 8 => 0.094094954682
  | _ => 0

theorem pilot_fullGroup1 :
    fullFormula 12223 12223 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 1) (BstLean.Part281.Groups.groupProfile 1) 1.25 ≤ pilotGroupCentre 1 := by
  apply pilot_full_formula_bound (X := (0.220845704627 : ℝ)) (T := (0.770098081416 : ℝ)) (R := (0.011263786123 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup2 :
    fullFormula 12223 12223 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 2) (BstLean.Part281.Groups.groupProfile 2) 1.25 ≤ pilotGroupCentre 2 := by
  apply pilot_full_formula_bound (X := (0.222412944838 : ℝ)) (T := (0.775935939689 : ℝ)) (R := (0.011382003448 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup3 :
    fullFormula 12223 12223 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 3) (BstLean.Part281.Groups.groupProfile 3) 1.25 ≤ pilotGroupCentre 3 := by
  apply pilot_full_formula_bound (X := (0.223959807548 : ℝ)) (T := (0.781730202020 : ℝ)) (R := (0.011499826438 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup4 :
    fullFormula 12223 12223 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 4) (BstLean.Part281.Groups.groupProfile 4) 1.25 ≤ pilotGroupCentre 4 := by
  apply pilot_full_formula_bound (X := (0.225486494853 : ℝ)) (T := (0.787481832331 : ℝ)) (R := (0.011617263827 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup5 :
    fullFormula 12223 12223 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 5) (BstLean.Part281.Groups.groupProfile 5) 1.25 ≤ pilotGroupCentre 5 := by
  apply pilot_full_formula_bound (X := (0.226993202494 : ℝ)) (T := (0.793191757238 : ℝ)) (R := (0.011734323989 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup6 :
    fullFormula 12223 12223 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 6) (BstLean.Part281.Groups.groupProfile 6) 1.25 ≤ pilotGroupCentre 6 := by
  apply pilot_full_formula_bound (X := (0.228480120706 : ℝ)) (T := (0.798860870240 : ℝ)) (R := (0.011851014996 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup7 :
    fullFormula 12223 12223 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 7) (BstLean.Part281.Groups.groupProfile 7) 1.25 ≤ pilotGroupCentre 7 := by
  apply pilot_full_formula_bound (X := (0.229947434992 : ℝ)) (T := (0.804490035675 : ℝ)) (R := (0.011967344684 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup8 :
    fullFormula 12223 12223 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 8) (BstLean.Part281.Groups.groupProfile 8) 1.25 ≤ pilotGroupCentre 8 := by
  apply pilot_full_formula_bound (X := (0.231395325068 : ℝ)) (T := (0.810080085548 : ℝ)) (R := (0.012083320569 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_group_full {g : Fin 10} (hg : BstLean.Part281.Groups.NeededGroup g) :
    fullFormula 12223 12223 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g) 1.25 ≤ pilotGroupCentre g := by
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => exact pilot_fullGroup1
  | ⟨2,h⟩ => exact pilot_fullGroup2
  | ⟨3,h⟩ => exact pilot_fullGroup3
  | ⟨4,h⟩ => exact pilot_fullGroup4
  | ⟨5,h⟩ => exact pilot_fullGroup5
  | ⟨6,h⟩ => exact pilot_fullGroup6
  | ⟨7,h⟩ => exact pilot_fullGroup7
  | ⟨8,h⟩ => exact pilot_fullGroup8
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)
end BstLean.Part281.N12223
namespace BstLean.Part281.N12223
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part281 (scalarRow12223 cell12223)
open BstLean.Part281.Groups (groupTheta groupProfile NeededGroup centreGroup)
theorem sourceCell10 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨10,by decide⟩).lower ∧ (scalarRow12223.table ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (scalarRow12223.table ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((471994609522106149011847/1000000000000000000000000) : ℝ) ∧ ((473194070474316763913033/1000000000000000000000000) : ℝ) ≤ (0.474440844 : ℝ) ∧
      ((473194070474316763913033/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((87088306483/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((7011264569757417/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((471994609522106149011847/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((87088306483/1000000000000) : ℝ) = (0.087088306483 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((471994609522106149011847/1000000000000000000000000) : ℚ) ∧ ((473194070474316763913033/1000000000000000000000000) : ℚ) ≤ (0.474440844 : ℚ) ∧
      ((473194070474316763913033/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((87088306483/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((7011264569757417/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((471994609522106149011847/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((87088306483/1000000000000) : ℚ) = (0.087088306483 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((471994609522106149011847/1000000000000000000000000) : ℝ) ∧ ((473194070474316763913033/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
      ((473194070474316763913033/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((87088306483/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((7011264569757417/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((471994609522106149011847/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((87088306483/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨10,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy10 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨10,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨10,by decide⟩).lower) ≤ (scalarRow12223.table ⟨10,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((471994609522106149011847/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((471994609522106149011847/1000000000000000000000000) : ℝ)) ≤ ((7011264569757417/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy10 (n := 12223) (by norm_num)
    (q := 1 - ((471994609522106149011847/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell11 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨11,by decide⟩).lower ∧ (scalarRow12223.table ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (scalarRow12223.table ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((59149258809289595489129/125000000000000000000000) : ℝ) ∧ ((237196765713263689407109/500000000000000000000000) : ℝ) ≤ (0.474440844 : ℝ) ∧
      ((237196765713263689407109/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((87088306483/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3502712081824757/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((59149258809289595489129/125000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((87088306483/1000000000000) : ℝ) = (0.087088306483 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((59149258809289595489129/125000000000000000000000) : ℚ) ∧ ((237196765713263689407109/500000000000000000000000) : ℚ) ≤ (0.474440844 : ℚ) ∧
      ((237196765713263689407109/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((87088306483/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3502712081824757/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((59149258809289595489129/125000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((87088306483/1000000000000) : ℚ) = (0.087088306483 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((59149258809289595489129/125000000000000000000000) : ℝ) ∧ ((237196765713263689407109/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
      ((237196765713263689407109/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((87088306483/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3502712081824757/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((59149258809289595489129/125000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((87088306483/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨11,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy11 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨11,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨11,by decide⟩).lower) ≤ (scalarRow12223.table ⟨11,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((59149258809289595489129/125000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((59149258809289595489129/125000000000000000000000) : ℝ)) ≤ ((3502712081824757/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy11 (n := 12223) (by norm_num)
    (q := 1 - ((59149258809289595489129/125000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell12 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨12,by decide⟩).lower ∧ (scalarRow12223.table ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (scalarRow12223.table ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((474393531426527378814217/1000000000000000000000000) : ℝ) ∧ ((475592992378737993715403/1000000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((475592992378737993715403/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88063712267/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((874948792514287/1250000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((474393531426527378814217/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((88063712267/1000000000000) : ℝ) = (0.088063712267 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((474393531426527378814217/1000000000000000000000000) : ℚ) ∧ ((475592992378737993715403/1000000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((475592992378737993715403/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((88063712267/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((874948792514287/1250000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((474393531426527378814217/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((88063712267/1000000000000) : ℚ) = (0.088063712267 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((474393531426527378814217/1000000000000000000000000) : ℝ) ∧ ((475592992378737993715403/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
      ((475592992378737993715403/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88063712267/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((874948792514287/1250000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((474393531426527378814217/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((88063712267/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨12,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy12 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨12,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨12,by decide⟩).lower) ≤ (scalarRow12223.table ⟨12,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((474393531426527378814217/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((474393531426527378814217/1000000000000000000000000) : ℝ)) ≤ ((874948792514287/1250000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy12 (n := 12223) (by norm_num)
    (q := 1 - ((474393531426527378814217/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell13 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨13,by decide⟩).lower ∧ (scalarRow12223.table ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (scalarRow12223.table ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((237796496189368996857701/500000000000000000000000) : ℝ) ∧ ((476792453330948608616587/1000000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((476792453330948608616587/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88063712267/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((87422038601201/125000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((237796496189368996857701/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((88063712267/1000000000000) : ℝ) = (0.088063712267 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((237796496189368996857701/500000000000000000000000) : ℚ) ∧ ((476792453330948608616587/1000000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((476792453330948608616587/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((88063712267/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((87422038601201/125000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((237796496189368996857701/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((88063712267/1000000000000) : ℚ) = (0.088063712267 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((237796496189368996857701/500000000000000000000000) : ℝ) ∧ ((476792453330948608616587/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
      ((476792453330948608616587/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88063712267/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((87422038601201/125000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((237796496189368996857701/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((88063712267/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨13,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy13 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨13,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨13,by decide⟩).lower) ≤ (scalarRow12223.table ⟨13,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((237796496189368996857701/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((237796496189368996857701/500000000000000000000000) : ℝ)) ≤ ((87422038601201/125000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy13 (n := 12223) (by norm_num)
    (q := 1 - ((237796496189368996857701/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell14 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨14,by decide⟩).lower ∧ (scalarRow12223.table ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (scalarRow12223.table ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((238396226665474304308293/500000000000000000000000) : ℝ) ∧ ((119497978570789805879443/250000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((119497978570789805879443/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88063712267/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6987942396583301/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((238396226665474304308293/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((88063712267/1000000000000) : ℝ) = (0.088063712267 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((238396226665474304308293/500000000000000000000000) : ℚ) ∧ ((119497978570789805879443/250000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((119497978570789805879443/250000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((88063712267/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6987942396583301/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((238396226665474304308293/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((88063712267/1000000000000) : ℚ) = (0.088063712267 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((238396226665474304308293/500000000000000000000000) : ℝ) ∧ ((119497978570789805879443/250000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
      ((119497978570789805879443/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88063712267/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6987942396583301/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((238396226665474304308293/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((88063712267/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨14,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy14 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨14,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨14,by decide⟩).lower) ≤ (scalarRow12223.table ⟨14,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((238396226665474304308293/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((238396226665474304308293/500000000000000000000000) : ℝ)) ≤ ((6987942396583301/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy14 (n := 12223) (by norm_num)
    (q := 1 - ((238396226665474304308293/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell15 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨15,by decide⟩).lower ∧ (scalarRow12223.table ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (scalarRow12223.table ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((477991914283159223517771/1000000000000000000000000) : ℝ) ∧ ((479191375235369838418957/1000000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((479191375235369838418957/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88063712267/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3491064127304119/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((477991914283159223517771/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((88063712267/1000000000000) : ℝ) = (0.088063712267 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((477991914283159223517771/1000000000000000000000000) : ℚ) ∧ ((479191375235369838418957/1000000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((479191375235369838418957/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((88063712267/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3491064127304119/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((477991914283159223517771/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((88063712267/1000000000000) : ℚ) = (0.088063712267 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((477991914283159223517771/1000000000000000000000000) : ℝ) ∧ ((479191375235369838418957/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
      ((479191375235369838418957/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88063712267/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3491064127304119/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((477991914283159223517771/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((88063712267/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨15,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy15 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨15,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨15,by decide⟩).lower) ≤ (scalarRow12223.table ⟨15,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((477991914283159223517771/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((477991914283159223517771/1000000000000000000000000) : ℝ)) ≤ ((3491064127304119/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy15 (n := 12223) (by norm_num)
    (q := 1 - ((477991914283159223517771/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell16 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨16,by decide⟩).lower ∧ (scalarRow12223.table ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (scalarRow12223.table ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((119797843808842459604739/250000000000000000000000) : ℝ) ∧ ((240195418093790226660071/500000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((240195418093790226660071/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88063712267/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3488160325623369/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((119797843808842459604739/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((88063712267/1000000000000) : ℝ) = (0.088063712267 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((119797843808842459604739/250000000000000000000000) : ℚ) ∧ ((240195418093790226660071/500000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((240195418093790226660071/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((88063712267/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3488160325623369/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((119797843808842459604739/250000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((88063712267/1000000000000) : ℚ) = (0.088063712267 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((119797843808842459604739/250000000000000000000000) : ℝ) ∧ ((240195418093790226660071/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
      ((240195418093790226660071/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88063712267/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3488160325623369/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((119797843808842459604739/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((88063712267/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨16,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy16 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨16,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨16,by decide⟩).lower) ≤ (scalarRow12223.table ⟨16,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((119797843808842459604739/250000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((119797843808842459604739/250000000000000000000000) : ℝ)) ≤ ((3488160325623369/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy16 (n := 12223) (by norm_num)
    (q := 1 - ((119797843808842459604739/250000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell17 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨17,by decide⟩).lower ∧ (scalarRow12223.table ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (scalarRow12223.table ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((480390836187580453320141/1000000000000000000000000) : ℝ) ∧ ((481590297139791068221327/1000000000000000000000000) : ℝ) ≤ (0.481661266 : ℝ) ∧
      ((481590297139791068221327/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88063712267/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((435657473476121/625000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((480390836187580453320141/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((88063712267/1000000000000) : ℝ) = (0.088063712267 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((480390836187580453320141/1000000000000000000000000) : ℚ) ∧ ((481590297139791068221327/1000000000000000000000000) : ℚ) ≤ (0.481661266 : ℚ) ∧
      ((481590297139791068221327/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((88063712267/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((435657473476121/625000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((480390836187580453320141/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((88063712267/1000000000000) : ℚ) = (0.088063712267 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((480390836187580453320141/1000000000000000000000000) : ℝ) ∧ ((481590297139791068221327/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
      ((481590297139791068221327/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((88063712267/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((435657473476121/625000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((480390836187580453320141/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((88063712267/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨17,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy17 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨17,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨17,by decide⟩).lower) ≤ (scalarRow12223.table ⟨17,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((480390836187580453320141/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((480390836187580453320141/1000000000000000000000000) : ℝ)) ≤ ((435657473476121/625000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy17 (n := 12223) (by norm_num)
    (q := 1 - ((480390836187580453320141/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell18 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨18,by decide⟩).lower ∧ (scalarRow12223.table ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (scalarRow12223.table ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((240795148569895534110663/500000000000000000000000) : ℝ) ∧ ((482789758092001683122511/1000000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((482789758092001683122511/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89042459827/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6964725016883991/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((240795148569895534110663/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((89042459827/1000000000000) : ℝ) = (0.089042459827 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((240795148569895534110663/500000000000000000000000) : ℚ) ∧ ((482789758092001683122511/1000000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((482789758092001683122511/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((89042459827/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6964725016883991/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((240795148569895534110663/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((89042459827/1000000000000) : ℚ) = (0.089042459827 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((240795148569895534110663/500000000000000000000000) : ℝ) ∧ ((482789758092001683122511/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
      ((482789758092001683122511/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89042459827/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6964725016883991/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((240795148569895534110663/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((89042459827/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨18,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy18 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨18,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨18,by decide⟩).lower) ≤ (scalarRow12223.table ⟨18,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((240795148569895534110663/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((240795148569895534110663/500000000000000000000000) : ℝ)) ≤ ((6964725016883991/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy18 (n := 12223) (by norm_num)
    (q := 1 - ((240795148569895534110663/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell19 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨19,by decide⟩).lower ∧ (scalarRow12223.table ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (scalarRow12223.table ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((48278975809200168312251/100000000000000000000000) : ℝ) ∧ ((30249326190263268626481/62500000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((30249326190263268626481/62500000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89042459827/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((695893696424981/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((48278975809200168312251/100000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((89042459827/1000000000000) : ℝ) = (0.089042459827 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((48278975809200168312251/100000000000000000000000) : ℚ) ∧ ((30249326190263268626481/62500000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((30249326190263268626481/62500000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((89042459827/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((695893696424981/1000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((48278975809200168312251/100000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((89042459827/1000000000000) : ℚ) = (0.089042459827 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((48278975809200168312251/100000000000000000000000) : ℝ) ∧ ((30249326190263268626481/62500000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
      ((30249326190263268626481/62500000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89042459827/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((695893696424981/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((48278975809200168312251/100000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((89042459827/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨19,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy19 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨19,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨19,by decide⟩).lower) ≤ (scalarRow12223.table ⟨19,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((48278975809200168312251/100000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((48278975809200168312251/100000000000000000000000) : ℝ)) ≤ ((695893696424981/1000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy19 (n := 12223) (by norm_num)
    (q := 1 - ((48278975809200168312251/100000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell20 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨20,by decide⟩).lower ∧ (scalarRow12223.table ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (scalarRow12223.table ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((96797843808842459604739/200000000000000000000000) : ℝ) ∧ ((485188679996422912924881/1000000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((485188679996422912924881/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89042459827/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6953155406962787/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((96797843808842459604739/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((89042459827/1000000000000) : ℝ) = (0.089042459827 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((96797843808842459604739/200000000000000000000000) : ℚ) ∧ ((485188679996422912924881/1000000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((485188679996422912924881/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((89042459827/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6953155406962787/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((96797843808842459604739/200000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((89042459827/1000000000000) : ℚ) = (0.089042459827 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((96797843808842459604739/200000000000000000000000) : ℝ) ∧ ((485188679996422912924881/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
      ((485188679996422912924881/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89042459827/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6953155406962787/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((96797843808842459604739/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((89042459827/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨20,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy20 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨20,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨20,by decide⟩).lower) ≤ (scalarRow12223.table ⟨20,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((96797843808842459604739/200000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((96797843808842459604739/200000000000000000000000) : ℝ)) ≤ ((6953155406962787/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy20 (n := 12223) (by norm_num)
    (q := 1 - ((96797843808842459604739/200000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell21 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨21,by decide⟩).lower ∧ (scalarRow12223.table ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (scalarRow12223.table ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((6064858499955286411561/12500000000000000000000) : ℝ) ∧ ((243194070474316763913033/500000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((243194070474316763913033/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89042459827/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1389476066862507/2000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((6064858499955286411561/12500000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((89042459827/1000000000000) : ℝ) = (0.089042459827 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((6064858499955286411561/12500000000000000000000) : ℚ) ∧ ((243194070474316763913033/500000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((243194070474316763913033/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((89042459827/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1389476066862507/2000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((6064858499955286411561/12500000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((89042459827/1000000000000) : ℚ) = (0.089042459827 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((6064858499955286411561/12500000000000000000000) : ℝ) ∧ ((243194070474316763913033/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
      ((243194070474316763913033/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89042459827/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1389476066862507/2000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((6064858499955286411561/12500000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((89042459827/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨21,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy21 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨21,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨21,by decide⟩).lower) ≤ (scalarRow12223.table ⟨21,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((6064858499955286411561/12500000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((6064858499955286411561/12500000000000000000000) : ℝ)) ≤ ((1389476066862507/2000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy21 (n := 12223) (by norm_num)
    (q := 1 - ((6064858499955286411561/12500000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell22 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨22,by decide⟩).lower ∧ (scalarRow12223.table ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (scalarRow12223.table ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((97277628189726705565213/200000000000000000000000) : ℝ) ∧ ((487587601900844142727251/1000000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((487587601900844142727251/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89042459827/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1735402933907657/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((97277628189726705565213/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((89042459827/1000000000000) : ℝ) = (0.089042459827 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((97277628189726705565213/200000000000000000000000) : ℚ) ∧ ((487587601900844142727251/1000000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((487587601900844142727251/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((89042459827/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1735402933907657/2500000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((97277628189726705565213/200000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((89042459827/1000000000000) : ℚ) = (0.089042459827 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((97277628189726705565213/200000000000000000000000) : ℝ) ∧ ((487587601900844142727251/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
      ((487587601900844142727251/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89042459827/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1735402933907657/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((97277628189726705565213/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((89042459827/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨22,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy22 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨22,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨22,by decide⟩).lower) ≤ (scalarRow12223.table ⟨22,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((97277628189726705565213/200000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((97277628189726705565213/200000000000000000000000) : ℝ)) ≤ ((1735402933907657/2500000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy22 (n := 12223) (by norm_num)
    (q := 1 - ((97277628189726705565213/200000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell23 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨23,by decide⟩).lower ∧ (scalarRow12223.table ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (scalarRow12223.table ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((1950350407603376570909/4000000000000000000000) : ℝ) ∧ ((97757412570610951525687/200000000000000000000000) : ℝ) ≤ (0.488881687 : ℝ) ∧
      ((97757412570610951525687/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89042459827/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((216745300009073/312500000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((1950350407603376570909/4000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((89042459827/1000000000000) : ℝ) = (0.089042459827 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((1950350407603376570909/4000000000000000000000) : ℚ) ∧ ((97757412570610951525687/200000000000000000000000) : ℚ) ≤ (0.488881687 : ℚ) ∧
      ((97757412570610951525687/200000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((89042459827/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((216745300009073/312500000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((1950350407603376570909/4000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((89042459827/1000000000000) : ℚ) = (0.089042459827 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((1950350407603376570909/4000000000000000000000) : ℝ) ∧ ((97757412570610951525687/200000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
      ((97757412570610951525687/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((89042459827/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((216745300009073/312500000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((1950350407603376570909/4000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((89042459827/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨23,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy23 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨23,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨23,by decide⟩).lower) ≤ (scalarRow12223.table ⟨23,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((1950350407603376570909/4000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((1950350407603376570909/4000000000000000000000) : ℝ)) ≤ ((216745300009073/312500000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy23 (n := 12223) (by norm_num)
    (q := 1 - ((1950350407603376570909/4000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell24 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨24,by decide⟩).lower ∧ (scalarRow12223.table ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (scalarRow12223.table ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((244393531426527378814217/500000000000000000000000) : ℝ) ∧ ((24499326190263268626481/50000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((24499326190263268626481/50000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11253389919/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6930093917706369/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((244393531426527378814217/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((11253389919/125000000000) : ℝ) = (0.090027119352 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((244393531426527378814217/500000000000000000000000) : ℚ) ∧ ((24499326190263268626481/50000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((24499326190263268626481/50000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((11253389919/125000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6930093917706369/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((244393531426527378814217/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((11253389919/125000000000) : ℚ) = (0.090027119352 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((244393531426527378814217/500000000000000000000000) : ℝ) ∧ ((24499326190263268626481/50000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
      ((24499326190263268626481/50000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11253389919/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6930093917706369/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((244393531426527378814217/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((11253389919/125000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨24,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy24 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨24,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨24,by decide⟩).lower) ≤ (scalarRow12223.table ⟨24,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((244393531426527378814217/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((244393531426527378814217/500000000000000000000000) : ℝ)) ≤ ((6930093917706369/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy24 (n := 12223) (by norm_num)
    (q := 1 - ((244393531426527378814217/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell25 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨25,by decide⟩).lower ∧ (scalarRow12223.table ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (scalarRow12223.table ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((489986523805265372529619/1000000000000000000000000) : ℝ) ∧ ((98237196951495197486161/200000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((98237196951495197486161/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11253389919/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1731086169333657/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((489986523805265372529619/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((11253389919/125000000000) : ℝ) = (0.090027119352 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((489986523805265372529619/1000000000000000000000000) : ℚ) ∧ ((98237196951495197486161/200000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((98237196951495197486161/200000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((11253389919/125000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1731086169333657/2500000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((489986523805265372529619/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((11253389919/125000000000) : ℚ) = (0.090027119352 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((489986523805265372529619/1000000000000000000000000) : ℝ) ∧ ((98237196951495197486161/200000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
      ((98237196951495197486161/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11253389919/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1731086169333657/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((489986523805265372529619/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((11253389919/125000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨25,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy25 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨25,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨25,by decide⟩).lower) ≤ (scalarRow12223.table ⟨25,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((489986523805265372529619/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((489986523805265372529619/1000000000000000000000000) : ℝ)) ≤ ((1731086169333657/2500000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy25 (n := 12223) (by norm_num)
    (q := 1 - ((489986523805265372529619/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell26 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨26,by decide⟩).lower ∧ (scalarRow12223.table ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (scalarRow12223.table ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((122796496189368996857701/250000000000000000000000) : ℝ) ∧ ((49238544570968660233199/100000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((49238544570968660233199/100000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11253389919/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6918601868671941/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((122796496189368996857701/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((11253389919/125000000000) : ℝ) = (0.090027119352 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((122796496189368996857701/250000000000000000000000) : ℚ) ∧ ((49238544570968660233199/100000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((49238544570968660233199/100000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((11253389919/125000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6918601868671941/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((122796496189368996857701/250000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((11253389919/125000000000) : ℚ) = (0.090027119352 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((122796496189368996857701/250000000000000000000000) : ℝ) ∧ ((49238544570968660233199/100000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
      ((49238544570968660233199/100000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11253389919/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6918601868671941/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((122796496189368996857701/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((11253389919/125000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨26,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy26 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨26,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨26,by decide⟩).lower) ≤ (scalarRow12223.table ⟨26,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((122796496189368996857701/250000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((122796496189368996857701/250000000000000000000000) : ℝ)) ≤ ((6918601868671941/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy26 (n := 12223) (by norm_num)
    (q := 1 - ((122796496189368996857701/250000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell27 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨27,by decide⟩).lower ∧ (scalarRow12223.table ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (scalarRow12223.table ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((492385445709686602331989/1000000000000000000000000) : ℝ) ∧ ((246792453330948608616587/500000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((246792453330948608616587/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11253389919/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6912865481255821/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((492385445709686602331989/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((11253389919/125000000000) : ℝ) = (0.090027119352 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((492385445709686602331989/1000000000000000000000000) : ℚ) ∧ ((246792453330948608616587/500000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((246792453330948608616587/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((11253389919/125000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6912865481255821/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((492385445709686602331989/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((11253389919/125000000000) : ℚ) = (0.090027119352 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((492385445709686602331989/1000000000000000000000000) : ℝ) ∧ ((246792453330948608616587/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
      ((246792453330948608616587/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11253389919/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6912865481255821/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((492385445709686602331989/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((11253389919/125000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨27,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy27 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨27,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨27,by decide⟩).lower) ≤ (scalarRow12223.table ⟨27,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((492385445709686602331989/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((492385445709686602331989/1000000000000000000000000) : ℝ)) ≤ ((6912865481255821/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy27 (n := 12223) (by norm_num)
    (q := 1 - ((492385445709686602331989/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell28 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨28,by decide⟩).lower ∧ (scalarRow12223.table ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (scalarRow12223.table ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((493584906661897217233173/1000000000000000000000000) : ℝ) ∧ ((494784367614107832134359/1000000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((494784367614107832134359/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11253389919/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((863391938083027/1250000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((493584906661897217233173/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((11253389919/125000000000) : ℝ) = (0.090027119352 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((493584906661897217233173/1000000000000000000000000) : ℚ) ∧ ((494784367614107832134359/1000000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((494784367614107832134359/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((11253389919/125000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((863391938083027/1250000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((493584906661897217233173/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((11253389919/125000000000) : ℚ) = (0.090027119352 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((493584906661897217233173/1000000000000000000000000) : ℝ) ∧ ((494784367614107832134359/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
      ((494784367614107832134359/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11253389919/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((863391938083027/1250000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((493584906661897217233173/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((11253389919/125000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨28,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy28 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨28,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨28,by decide⟩).lower) ≤ (scalarRow12223.table ⟨28,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((493584906661897217233173/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((493584906661897217233173/1000000000000000000000000) : ℝ)) ≤ ((863391938083027/1250000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy28 (n := 12223) (by norm_num)
    (q := 1 - ((493584906661897217233173/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell29 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨29,by decide⟩).lower ∧ (scalarRow12223.table ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (scalarRow12223.table ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((247392183807053916067179/500000000000000000000000) : ℝ) ∧ ((61997978570789805879443/125000000000000000000000) : ℝ) ≤ (0.496102109 : ℝ) ∧
      ((61997978570789805879443/125000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11253389919/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6901411928515259/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((247392183807053916067179/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((11253389919/125000000000) : ℝ) = (0.090027119352 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((247392183807053916067179/500000000000000000000000) : ℚ) ∧ ((61997978570789805879443/125000000000000000000000) : ℚ) ≤ (0.496102109 : ℚ) ∧
      ((61997978570789805879443/125000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((11253389919/125000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6901411928515259/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((247392183807053916067179/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((11253389919/125000000000) : ℚ) = (0.090027119352 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((247392183807053916067179/500000000000000000000000) : ℝ) ∧ ((61997978570789805879443/125000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
      ((61997978570789805879443/125000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((11253389919/125000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6901411928515259/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((247392183807053916067179/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((11253389919/125000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨29,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy29 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨29,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨29,by decide⟩).lower) ≤ (scalarRow12223.table ⟨29,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((247392183807053916067179/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((247392183807053916067179/500000000000000000000000) : ℝ)) ≤ ((6901411928515259/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy29 (n := 12223) (by norm_num)
    (q := 1 - ((247392183807053916067179/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell30 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨30,by decide⟩).lower ∧ (scalarRow12223.table ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (scalarRow12223.table ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((495983828566318447035543/1000000000000000000000000) : ℝ) ∧ ((497183289518529061936729/1000000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((497183289518529061936729/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22755188353/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((275827789698681/400000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((495983828566318447035543/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22755188353/250000000000) : ℝ) = (0.091020753412 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((495983828566318447035543/1000000000000000000000000) : ℚ) ∧ ((497183289518529061936729/1000000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((497183289518529061936729/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22755188353/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((275827789698681/400000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((495983828566318447035543/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22755188353/250000000000) : ℚ) = (0.091020753412 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((495983828566318447035543/1000000000000000000000000) : ℝ) ∧ ((497183289518529061936729/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
      ((497183289518529061936729/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22755188353/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((275827789698681/400000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((495983828566318447035543/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22755188353/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨30,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy30 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨30,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨30,by decide⟩).lower) ≤ (scalarRow12223.table ⟨30,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((495983828566318447035543/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((495983828566318447035543/1000000000000000000000000) : ℝ)) ≤ ((275827789698681/400000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy30 (n := 12223) (by norm_num)
    (q := 1 - ((495983828566318447035543/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell31 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨31,by decide⟩).lower ∧ (scalarRow12223.table ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (scalarRow12223.table ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((62147911189816132742091/125000000000000000000000) : ℝ) ∧ ((249191375235369838418957/500000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((249191375235369838418957/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22755188353/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6889983936217291/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((62147911189816132742091/125000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22755188353/250000000000) : ℝ) = (0.091020753412 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((62147911189816132742091/125000000000000000000000) : ℚ) ∧ ((249191375235369838418957/500000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((249191375235369838418957/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22755188353/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6889983936217291/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((62147911189816132742091/125000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22755188353/250000000000) : ℚ) = (0.091020753412 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((62147911189816132742091/125000000000000000000000) : ℝ) ∧ ((249191375235369838418957/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
      ((249191375235369838418957/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22755188353/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6889983936217291/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((62147911189816132742091/125000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22755188353/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨31,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy31 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨31,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨31,by decide⟩).lower) ≤ (scalarRow12223.table ⟨31,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((62147911189816132742091/125000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((62147911189816132742091/125000000000000000000000) : ℝ)) ≤ ((6889983936217291/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy31 (n := 12223) (by norm_num)
    (q := 1 - ((62147911189816132742091/125000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell32 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨32,by decide⟩).lower ∧ (scalarRow12223.table ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (scalarRow12223.table ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((498382750470739676837913/1000000000000000000000000) : ℝ) ∧ ((249791105711475145869549/500000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((249791105711475145869549/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22755188353/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1376855899900659/2000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((498382750470739676837913/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22755188353/250000000000) : ℝ) = (0.091020753412 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((498382750470739676837913/1000000000000000000000000) : ℚ) ∧ ((249791105711475145869549/500000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((249791105711475145869549/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22755188353/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1376855899900659/2000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((498382750470739676837913/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22755188353/250000000000) : ℚ) = (0.091020753412 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((498382750470739676837913/1000000000000000000000000) : ℝ) ∧ ((249791105711475145869549/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
      ((249791105711475145869549/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22755188353/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1376855899900659/2000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((498382750470739676837913/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22755188353/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨32,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy32 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨32,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨32,by decide⟩).lower) ≤ (scalarRow12223.table ⟨32,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((498382750470739676837913/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((498382750470739676837913/1000000000000000000000000) : ℝ)) ≤ ((1376855899900659/2000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy32 (n := 12223) (by norm_num)
    (q := 1 - ((498382750470739676837913/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell33 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨33,by decide⟩).lower ∧ (scalarRow12223.table ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (scalarRow12223.table ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((499582211422950291739097/1000000000000000000000000) : ℝ) ∧ ((500781672375160906640283/1000000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((500781672375160906640283/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22755188353/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1375716284420299/2000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((499582211422950291739097/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22755188353/250000000000) : ℝ) = (0.091020753412 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((499582211422950291739097/1000000000000000000000000) : ℚ) ∧ ((500781672375160906640283/1000000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((500781672375160906640283/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22755188353/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1375716284420299/2000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((499582211422950291739097/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22755188353/250000000000) : ℚ) = (0.091020753412 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((499582211422950291739097/1000000000000000000000000) : ℝ) ∧ ((500781672375160906640283/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
      ((500781672375160906640283/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22755188353/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1375716284420299/2000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((499582211422950291739097/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22755188353/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨33,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy33 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨33,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨33,by decide⟩).lower) ≤ (scalarRow12223.table ⟨33,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((499582211422950291739097/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((499582211422950291739097/1000000000000000000000000) : ℝ)) ≤ ((1375716284420299/2000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy33 (n := 12223) (by norm_num)
    (q := 1 - ((499582211422950291739097/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell34 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨34,by decide⟩).lower ∧ (scalarRow12223.table ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (scalarRow12223.table ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((250390836187580453320141/500000000000000000000000) : ℝ) ∧ ((125495283331842880385367/250000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((125495283331842880385367/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22755188353/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6872889693827337/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((250390836187580453320141/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22755188353/250000000000) : ℝ) = (0.091020753412 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((250390836187580453320141/500000000000000000000000) : ℚ) ∧ ((125495283331842880385367/250000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((125495283331842880385367/250000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22755188353/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6872889693827337/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((250390836187580453320141/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22755188353/250000000000) : ℚ) = (0.091020753412 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((250390836187580453320141/500000000000000000000000) : ℝ) ∧ ((125495283331842880385367/250000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
      ((125495283331842880385367/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22755188353/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6872889693827337/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((250390836187580453320141/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22755188353/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨34,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy34 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨34,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨34,by decide⟩).lower) ≤ (scalarRow12223.table ⟨34,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((250390836187580453320141/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((250390836187580453320141/500000000000000000000000) : ℝ)) ≤ ((6872889693827337/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy34 (n := 12223) (by norm_num)
    (q := 1 - ((250390836187580453320141/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell35 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨35,by decide⟩).lower ∧ (scalarRow12223.table ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (scalarRow12223.table ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((501981133327371521541467/1000000000000000000000000) : ℝ) ∧ ((503180594279582136442653/1000000000000000000000000) : ℝ) ≤ (0.503322531 : ℝ) ∧
      ((503180594279582136442653/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22755188353/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6867204304535019/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((501981133327371521541467/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((22755188353/250000000000) : ℝ) = (0.091020753412 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((501981133327371521541467/1000000000000000000000000) : ℚ) ∧ ((503180594279582136442653/1000000000000000000000000) : ℚ) ≤ (0.503322531 : ℚ) ∧
      ((503180594279582136442653/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((22755188353/250000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6867204304535019/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((501981133327371521541467/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((22755188353/250000000000) : ℚ) = (0.091020753412 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((501981133327371521541467/1000000000000000000000000) : ℝ) ∧ ((503180594279582136442653/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
      ((503180594279582136442653/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((22755188353/250000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6867204304535019/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((501981133327371521541467/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((22755188353/250000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨35,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy35 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨35,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨35,by decide⟩).lower) ≤ (scalarRow12223.table ⟨35,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((501981133327371521541467/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((501981133327371521541467/1000000000000000000000000) : ℝ)) ≤ ((6867204304535019/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy35 (n := 12223) (by norm_num)
    (q := 1 - ((501981133327371521541467/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell36 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨36,by decide⟩).lower ∧ (scalarRow12223.table ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (scalarRow12223.table ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((125795148569895534110663/250000000000000000000000) : ℝ) ∧ ((504380055231792751343837/1000000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((504380055231792751343837/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((46013491913/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3430762622058629/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((125795148569895534110663/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((46013491913/500000000000) : ℝ) = (0.092026983826 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((125795148569895534110663/250000000000000000000000) : ℚ) ∧ ((504380055231792751343837/1000000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((504380055231792751343837/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((46013491913/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3430762622058629/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((125795148569895534110663/250000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((46013491913/500000000000) : ℚ) = (0.092026983826 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((125795148569895534110663/250000000000000000000000) : ℝ) ∧ ((504380055231792751343837/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
      ((504380055231792751343837/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((46013491913/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3430762622058629/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((125795148569895534110663/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((46013491913/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨36,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy36 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨36,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨36,by decide⟩).lower) ≤ (scalarRow12223.table ⟨36,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((125795148569895534110663/250000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((125795148569895534110663/250000000000000000000000) : ℝ)) ≤ ((3430762622058629/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy36 (n := 12223) (by norm_num)
    (q := 1 - ((125795148569895534110663/250000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell37 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨37,by decide⟩).lower ∧ (scalarRow12223.table ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (scalarRow12223.table ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((126095013807948187835959/250000000000000000000000) : ℝ) ∧ ((252789758092001683122511/500000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((252789758092001683122511/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((46013491913/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6855852502505061/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((126095013807948187835959/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((46013491913/500000000000) : ℝ) = (0.092026983826 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((126095013807948187835959/250000000000000000000000) : ℚ) ∧ ((252789758092001683122511/500000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((252789758092001683122511/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((46013491913/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6855852502505061/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((126095013807948187835959/250000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((46013491913/500000000000) : ℚ) = (0.092026983826 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((126095013807948187835959/250000000000000000000000) : ℝ) ∧ ((252789758092001683122511/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
      ((252789758092001683122511/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((46013491913/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6855852502505061/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((126095013807948187835959/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((46013491913/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨37,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy37 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨37,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨37,by decide⟩).lower) ≤ (scalarRow12223.table ⟨37,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((126095013807948187835959/250000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((126095013807948187835959/250000000000000000000000) : ℝ)) ≤ ((6855852502505061/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy37 (n := 12223) (by norm_num)
    (q := 1 - ((126095013807948187835959/250000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell38 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨38,by decide⟩).lower ∧ (scalarRow12223.table ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (scalarRow12223.table ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((505579516184003366245021/1000000000000000000000000) : ℝ) ∧ ((506778977136213981146207/1000000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((506778977136213981146207/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((46013491913/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6850186069667497/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((505579516184003366245021/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((46013491913/500000000000) : ℝ) = (0.092026983826 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((505579516184003366245021/1000000000000000000000000) : ℚ) ∧ ((506778977136213981146207/1000000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((506778977136213981146207/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((46013491913/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6850186069667497/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((505579516184003366245021/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((46013491913/500000000000) : ℚ) = (0.092026983826 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((505579516184003366245021/1000000000000000000000000) : ℝ) ∧ ((506778977136213981146207/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
      ((506778977136213981146207/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((46013491913/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6850186069667497/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((505579516184003366245021/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((46013491913/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨38,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy38 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨38,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨38,by decide⟩).lower) ≤ (scalarRow12223.table ⟨38,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((505579516184003366245021/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((505579516184003366245021/1000000000000000000000000) : ℝ)) ≤ ((6850186069667497/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy38 (n := 12223) (by norm_num)
    (q := 1 - ((505579516184003366245021/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell39 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨39,by decide⟩).lower ∧ (scalarRow12223.table ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (scalarRow12223.table ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((253389488568106990573103/500000000000000000000000) : ℝ) ∧ ((15874326190263268626481/31250000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((15874326190263268626481/31250000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((46013491913/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6844525935611473/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((253389488568106990573103/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((46013491913/500000000000) : ℝ) = (0.092026983826 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((253389488568106990573103/500000000000000000000000) : ℚ) ∧ ((15874326190263268626481/31250000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((15874326190263268626481/31250000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((46013491913/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6844525935611473/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((253389488568106990573103/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((46013491913/500000000000) : ℚ) = (0.092026983826 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((253389488568106990573103/500000000000000000000000) : ℝ) ∧ ((15874326190263268626481/31250000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
      ((15874326190263268626481/31250000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((46013491913/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6844525935611473/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((253389488568106990573103/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((46013491913/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨39,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy39 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨39,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨39,by decide⟩).lower) ≤ (scalarRow12223.table ⟨39,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((253389488568106990573103/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((253389488568106990573103/500000000000000000000000) : ℝ)) ≤ ((6844525935611473/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy39 (n := 12223) (by norm_num)
    (q := 1 - ((253389488568106990573103/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell40 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨40,by decide⟩).lower ∧ (scalarRow12223.table ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (scalarRow12223.table ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((507978438088424596047391/1000000000000000000000000) : ℝ) ∧ ((509177899040635210948577/1000000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((509177899040635210948577/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((46013491913/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3419436045190751/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((507978438088424596047391/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((46013491913/500000000000) : ℝ) = (0.092026983826 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((507978438088424596047391/1000000000000000000000000) : ℚ) ∧ ((509177899040635210948577/1000000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((509177899040635210948577/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((46013491913/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3419436045190751/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((507978438088424596047391/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((46013491913/500000000000) : ℚ) = (0.092026983826 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((507978438088424596047391/1000000000000000000000000) : ℝ) ∧ ((509177899040635210948577/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
      ((509177899040635210948577/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((46013491913/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3419436045190751/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((507978438088424596047391/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((46013491913/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨40,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy40 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨40,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨40,by decide⟩).lower) ≤ (scalarRow12223.table ⟨40,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((507978438088424596047391/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((507978438088424596047391/1000000000000000000000000) : ℝ)) ≤ ((3419436045190751/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy40 (n := 12223) (by norm_num)
    (q := 1 - ((507978438088424596047391/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell41 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨41,by decide⟩).lower ∧ (scalarRow12223.table ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (scalarRow12223.table ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((15911809345019850342143/31250000000000000000000) : ℝ) ∧ ((510377359992845825849761/1000000000000000000000000) : ℝ) ≤ (0.510542952 : ℝ) ∧
      ((510377359992845825849761/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((46013491913/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1708306131014873/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((15911809345019850342143/31250000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((46013491913/500000000000) : ℝ) = (0.092026983826 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((15911809345019850342143/31250000000000000000000) : ℚ) ∧ ((510377359992845825849761/1000000000000000000000000) : ℚ) ≤ (0.510542952 : ℚ) ∧
      ((510377359992845825849761/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((46013491913/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1708306131014873/2500000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((15911809345019850342143/31250000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((46013491913/500000000000) : ℚ) = (0.092026983826 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((15911809345019850342143/31250000000000000000000) : ℝ) ∧ ((510377359992845825849761/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
      ((510377359992845825849761/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((46013491913/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1708306131014873/2500000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((15911809345019850342143/31250000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((46013491913/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨41,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy41 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨41,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨41,by decide⟩).lower) ≤ (scalarRow12223.table ⟨41,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((15911809345019850342143/31250000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((15911809345019850342143/31250000000000000000000) : ℝ)) ≤ ((1708306131014873/2500000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy41 (n := 12223) (by norm_num)
    (q := 1 - ((15911809345019850342143/31250000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell42 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨42,by decide⟩).lower ∧ (scalarRow12223.table ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (scalarRow12223.table ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((3189858499955286411561/6250000000000000000000) : ℝ) ∧ ((255788410472528220375473/500000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((255788410472528220375473/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93050063729/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3413791613382257/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((3189858499955286411561/6250000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((93050063729/1000000000000) : ℝ) = (0.093050063729 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((3189858499955286411561/6250000000000000000000) : ℚ) ∧ ((255788410472528220375473/500000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((255788410472528220375473/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((93050063729/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3413791613382257/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((3189858499955286411561/6250000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((93050063729/1000000000000) : ℚ) = (0.093050063729 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((3189858499955286411561/6250000000000000000000) : ℝ) ∧ ((255788410472528220375473/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
      ((255788410472528220375473/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93050063729/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3413791613382257/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((3189858499955286411561/6250000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((93050063729/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨42,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy42 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨42,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨42,by decide⟩).lower) ≤ (scalarRow12223.table ⟨42,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((3189858499955286411561/6250000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((3189858499955286411561/6250000000000000000000) : ℝ)) ≤ ((3413791613382257/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy42 (n := 12223) (by norm_num)
    (q := 1 - ((3189858499955286411561/6250000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell43 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨43,by decide⟩).lower ∧ (scalarRow12223.table ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (scalarRow12223.table ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((102315364189011288150189/200000000000000000000000) : ℝ) ∧ ((512776281897267055652131/1000000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((512776281897267055652131/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93050063729/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6821948188652591/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((102315364189011288150189/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((93050063729/1000000000000) : ℝ) = (0.093050063729 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((102315364189011288150189/200000000000000000000000) : ℚ) ∧ ((512776281897267055652131/1000000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((512776281897267055652131/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((93050063729/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6821948188652591/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((102315364189011288150189/200000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((93050063729/1000000000000) : ℚ) = (0.093050063729 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((102315364189011288150189/200000000000000000000000) : ℝ) ∧ ((512776281897267055652131/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
      ((512776281897267055652131/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93050063729/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6821948188652591/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((102315364189011288150189/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((93050063729/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨43,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy43 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨43,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨43,by decide⟩).lower) ≤ (scalarRow12223.table ⟨43,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((102315364189011288150189/200000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((102315364189011288150189/200000000000000000000000) : ℝ)) ≤ ((6821948188652591/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy43 (n := 12223) (by norm_num)
    (q := 1 - ((102315364189011288150189/200000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell44 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨44,by decide⟩).lower ∧ (scalarRow12223.table ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (scalarRow12223.table ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((51277628189726705565213/100000000000000000000000) : ℝ) ∧ ((128493935712369417638329/250000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((128493935712369417638329/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93050063729/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((21300998124739/31250000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((51277628189726705565213/100000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((93050063729/1000000000000) : ℝ) = (0.093050063729 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((51277628189726705565213/100000000000000000000000) : ℚ) ∧ ((128493935712369417638329/250000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((128493935712369417638329/250000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((93050063729/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((21300998124739/31250000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((51277628189726705565213/100000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((93050063729/1000000000000) : ℚ) = (0.093050063729 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((51277628189726705565213/100000000000000000000000) : ℝ) ∧ ((128493935712369417638329/250000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
      ((128493935712369417638329/250000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93050063729/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((21300998124739/31250000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((51277628189726705565213/100000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((93050063729/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨44,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy44 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨44,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨44,by decide⟩).lower) ≤ (scalarRow12223.table ⟨44,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((51277628189726705565213/100000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((51277628189726705565213/100000000000000000000000) : ℝ)) ≤ ((21300998124739/31250000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy44 (n := 12223) (by norm_num)
    (q := 1 - ((51277628189726705565213/100000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell45 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨45,by decide⟩).lower ∧ (scalarRow12223.table ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (scalarRow12223.table ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((102795148569895534110663/200000000000000000000000) : ℝ) ∧ ((515175203801688285454501/1000000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((515175203801688285454501/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93050063729/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6810696850785453/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((102795148569895534110663/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((93050063729/1000000000000) : ℝ) = (0.093050063729 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((102795148569895534110663/200000000000000000000000) : ℚ) ∧ ((515175203801688285454501/1000000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((515175203801688285454501/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((93050063729/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((6810696850785453/10000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((102795148569895534110663/200000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((93050063729/1000000000000) : ℚ) = (0.093050063729 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((102795148569895534110663/200000000000000000000000) : ℝ) ∧ ((515175203801688285454501/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
      ((515175203801688285454501/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93050063729/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((6810696850785453/10000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((102795148569895534110663/200000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((93050063729/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨45,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy45 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨45,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨45,by decide⟩).lower) ≤ (scalarRow12223.table ⟨45,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((102795148569895534110663/200000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((102795148569895534110663/200000000000000000000000) : ℝ)) ≤ ((6810696850785453/10000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy45 (n := 12223) (by norm_num)
    (q := 1 - ((102795148569895534110663/200000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell46 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨46,by decide⟩).lower ∧ (scalarRow12223.table ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (scalarRow12223.table ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((1030350407603376570909/2000000000000000000000) : ℝ) ∧ ((103274932950779780071137/200000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((103274932950779780071137/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93050063729/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((212658766610159/312500000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((1030350407603376570909/2000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((93050063729/1000000000000) : ℝ) = (0.093050063729 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((1030350407603376570909/2000000000000000000000) : ℚ) ∧ ((103274932950779780071137/200000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((103274932950779780071137/200000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((93050063729/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((212658766610159/312500000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((1030350407603376570909/2000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((93050063729/1000000000000) : ℚ) = (0.093050063729 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((1030350407603376570909/2000000000000000000000) : ℝ) ∧ ((103274932950779780071137/200000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
      ((103274932950779780071137/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93050063729/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((212658766610159/312500000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((1030350407603376570909/2000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((93050063729/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨46,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy46 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨46,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨46,by decide⟩).lower) ≤ (scalarRow12223.table ⟨46,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((1030350407603376570909/2000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((1030350407603376570909/2000000000000000000000) : ℝ)) ≤ ((212658766610159/312500000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy46 (n := 12223) (by norm_num)
    (q := 1 - ((1030350407603376570909/2000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell47 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨47,by decide⟩).lower ∧ (scalarRow12223.table ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (scalarRow12223.table ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((129093666188474725088921/250000000000000000000000) : ℝ) ∧ ((51757412570610951525687/100000000000000000000000) : ℝ) ≤ (0.517763374 : ℝ) ∧
      ((51757412570610951525687/100000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93050063729/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3399735216218527/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((129093666188474725088921/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((93050063729/1000000000000) : ℝ) = (0.093050063729 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((129093666188474725088921/250000000000000000000000) : ℚ) ∧ ((51757412570610951525687/100000000000000000000000) : ℚ) ≤ (0.517763374 : ℚ) ∧
      ((51757412570610951525687/100000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((93050063729/1000000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3399735216218527/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((129093666188474725088921/250000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((93050063729/1000000000000) : ℚ) = (0.093050063729 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((129093666188474725088921/250000000000000000000000) : ℝ) ∧ ((51757412570610951525687/100000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
      ((51757412570610951525687/100000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((93050063729/1000000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3399735216218527/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((129093666188474725088921/250000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((93050063729/1000000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨47,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy47 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨47,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨47,by decide⟩).lower) ≤ (scalarRow12223.table ⟨47,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((129093666188474725088921/250000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((129093666188474725088921/250000000000000000000000) : ℝ)) ≤ ((3399735216218527/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy47 (n := 12223) (by norm_num)
    (q := 1 - ((129093666188474725088921/250000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell48 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨48,by decide⟩).lower ∧ (scalarRow12223.table ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (scalarRow12223.table ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((517574125706109515256869/1000000000000000000000000) : ℝ) ∧ ((103754717331664026031611/200000000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((103754717331664026031611/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((47047477341/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3396933271929453/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((517574125706109515256869/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((47047477341/500000000000) : ℝ) = (0.094094954682 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((517574125706109515256869/1000000000000000000000000) : ℚ) ∧ ((103754717331664026031611/200000000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((103754717331664026031611/200000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((47047477341/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((3396933271929453/5000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((517574125706109515256869/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((47047477341/500000000000) : ℚ) = (0.094094954682 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((517574125706109515256869/1000000000000000000000000) : ℝ) ∧ ((103754717331664026031611/200000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
      ((103754717331664026031611/200000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((47047477341/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((3396933271929453/5000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((517574125706109515256869/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((47047477341/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨48,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy48 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨48,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨48,by decide⟩).lower) ≤ (scalarRow12223.table ⟨48,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((517574125706109515256869/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((517574125706109515256869/1000000000000000000000000) : ℝ)) ≤ ((3396933271929453/5000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy48 (n := 12223) (by norm_num)
    (q := 1 - ((517574125706109515256869/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell49 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨49,by decide⟩).lower ∧ (scalarRow12223.table ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (scalarRow12223.table ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((259386793329160065079027/500000000000000000000000) : ℝ) ∧ ((12999326190263268626481/25000000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((12999326190263268626481/25000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((47047477341/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((678826885616387/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((259386793329160065079027/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((47047477341/500000000000) : ℝ) = (0.094094954682 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((259386793329160065079027/500000000000000000000000) : ℚ) ∧ ((12999326190263268626481/25000000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((12999326190263268626481/25000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((47047477341/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((678826885616387/1000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((259386793329160065079027/500000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((47047477341/500000000000) : ℚ) = (0.094094954682 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((259386793329160065079027/500000000000000000000000) : ℝ) ∧ ((12999326190263268626481/25000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
      ((12999326190263268626481/25000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((47047477341/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((678826885616387/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((259386793329160065079027/500000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((47047477341/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨49,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy49 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨49,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨49,by decide⟩).lower) ≤ (scalarRow12223.table ⟨49,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((259386793329160065079027/500000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((259386793329160065079027/500000000000000000000000) : ℝ)) ≤ ((678826885616387/1000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy49 (n := 12223) (by norm_num)
    (q := 1 - ((259386793329160065079027/500000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell50 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨50,by decide⟩).lower ∧ (scalarRow12223.table ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (scalarRow12223.table ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((519973047610530745059239/1000000000000000000000000) : ℝ) ∧ ((65146563570342669995053/125000000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((65146563570342669995053/125000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((47047477341/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1356535471952129/2000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((519973047610530745059239/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((47047477341/500000000000) : ℝ) = (0.094094954682 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((519973047610530745059239/1000000000000000000000000) : ℚ) ∧ ((65146563570342669995053/125000000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((65146563570342669995053/125000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((47047477341/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((1356535471952129/2000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((519973047610530745059239/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((47047477341/500000000000) : ℚ) = (0.094094954682 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((519973047610530745059239/1000000000000000000000000) : ℝ) ∧ ((65146563570342669995053/125000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
      ((65146563570342669995053/125000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((47047477341/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((1356535471952129/2000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((519973047610530745059239/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((47047477341/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨50,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy50 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨50,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨50,by decide⟩).lower) ≤ (scalarRow12223.table ⟨50,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((519973047610530745059239/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((519973047610530745059239/1000000000000000000000000) : ℝ)) ≤ ((1356535471952129/2000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy50 (n := 12223) (by norm_num)
    (q := 1 - ((519973047610530745059239/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell51 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨51,by decide⟩).lower ∧ (scalarRow12223.table ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (scalarRow12223.table ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((521172508562741359960423/1000000000000000000000000) : ℝ) ∧ ((522371969514951974861609/1000000000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((522371969514951974861609/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((47047477341/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((677709204509319/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((521172508562741359960423/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((47047477341/500000000000) : ℝ) = (0.094094954682 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((521172508562741359960423/1000000000000000000000000) : ℚ) ∧ ((522371969514951974861609/1000000000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((522371969514951974861609/1000000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((47047477341/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((677709204509319/1000000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((521172508562741359960423/1000000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((47047477341/500000000000) : ℚ) = (0.094094954682 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((521172508562741359960423/1000000000000000000000000) : ℝ) ∧ ((522371969514951974861609/1000000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
      ((522371969514951974861609/1000000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((47047477341/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((677709204509319/1000000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((521172508562741359960423/1000000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((47047477341/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨51,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy51 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨51,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨51,by decide⟩).lower) ≤ (scalarRow12223.table ⟨51,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((521172508562741359960423/1000000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((521172508562741359960423/1000000000000000000000000) : ℝ)) ≤ ((677709204509319/1000000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy51 (n := 12223) (by norm_num)
    (q := 1 - ((521172508562741359960423/1000000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem sourceCell52 :
    (0.46 : ℝ) ≤ (scalarRow12223.table ⟨52,by decide⟩).lower ∧ (scalarRow12223.table ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (scalarRow12223.table ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  first
  | change (0.46 : ℝ) ≤ ((65296496189368996857701/125000000000000000000000) : ℝ) ∧ ((261785715233581294881397/500000000000000000000000) : ℝ) ≤ (0.524983796 : ℝ) ∧
      ((261785715233581294881397/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((47047477341/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((423219556415033/625000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((65296496189368996857701/125000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧ ((47047477341/500000000000) : ℝ) = (0.094094954682 : ℝ)
    exact_mod_cast (show (0.46 : ℚ) ≤ ((65296496189368996857701/125000000000000000000000) : ℚ) ∧ ((261785715233581294881397/500000000000000000000000) : ℚ) ≤ (0.524983796 : ℚ) ∧
      ((261785715233581294881397/500000000000000000000000) : ℚ) ≤ (0.532 : ℚ) ∧ ((47047477341/500000000000) : ℚ) ≤ (0.1 : ℚ) ∧ ((423219556415033/625000000000000) : ℚ) ≤ (1 : ℚ) ∧
      (1 - ((65296496189368996857701/125000000000000000000000) : ℚ)) ∈ Icc (-1 : ℚ) 1 ∧ ((47047477341/500000000000) : ℚ) = (0.094094954682 : ℚ) from by decide)
  | change (0.46 : ℝ) ≤ ((65296496189368996857701/125000000000000000000000) : ℝ) ∧ ((261785715233581294881397/500000000000000000000000) : ℝ) ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
      ((261785715233581294881397/500000000000000000000000) : ℝ) ≤ (0.532 : ℝ) ∧ ((47047477341/500000000000) : ℝ) ≤ (0.1 : ℝ) ∧ ((423219556415033/625000000000000) : ℝ) ≤ (1 : ℝ) ∧
      (1 - ((65296496189368996857701/125000000000000000000000) : ℝ)) ∈ Icc (-1 : ℝ) 1 ∧
      ((47047477341/500000000000) : ℝ) = pilotGroupCentre (centreGroup ⟨52,by decide⟩)
    norm_num [groupTheta,centreGroup,BstLean.Part253.centreGroup,pilotGroupCentre]

theorem upperEnergy52 :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table ⟨52,by decide⟩).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table ⟨52,by decide⟩).lower) ≤ (scalarRow12223.table ⟨52,by decide⟩).energy := by
  change energyRatio 12223 (gMinus 12223) (1 - ((65296496189368996857701/125000000000000000000000) : ℝ)) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - ((65296496189368996857701/125000000000000000000000) : ℝ)) ≤ ((423219556415033/625000000000000) : ℝ)
  have E := BstLean.Part281.UE.uniformEnergy52 (n := 12223) (by norm_num)
    (q := 1 - ((65296496189368996857701/125000000000000000000000) : ℝ)) (by norm_num) (by norm_num)
  exact ⟨E.1,E.2.trans (by norm_num)⟩

theorem source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (scalarRow12223.table i).lower ∧ (scalarRow12223.table i).upper ≤ groupTheta (centreGroup i) ∧
    (scalarRow12223.table i).upper ≤ (0.532 : ℝ) ∧ (scalarRow12223.table i).centre ≤ (0.1 : ℝ) ∧ (scalarRow12223.table i).energy ≤ (1 : ℝ) ∧
    (1 - (scalarRow12223.table i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (scalarRow12223.table i).centre = pilotGroupCentre (centreGroup i) := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨2,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨3,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨4,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨5,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨6,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨7,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨8,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨9,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨10,h⟩ => exact sourceCell10
  | ⟨11,h⟩ => exact sourceCell11
  | ⟨12,h⟩ => exact sourceCell12
  | ⟨13,h⟩ => exact sourceCell13
  | ⟨14,h⟩ => exact sourceCell14
  | ⟨15,h⟩ => exact sourceCell15
  | ⟨16,h⟩ => exact sourceCell16
  | ⟨17,h⟩ => exact sourceCell17
  | ⟨18,h⟩ => exact sourceCell18
  | ⟨19,h⟩ => exact sourceCell19
  | ⟨20,h⟩ => exact sourceCell20
  | ⟨21,h⟩ => exact sourceCell21
  | ⟨22,h⟩ => exact sourceCell22
  | ⟨23,h⟩ => exact sourceCell23
  | ⟨24,h⟩ => exact sourceCell24
  | ⟨25,h⟩ => exact sourceCell25
  | ⟨26,h⟩ => exact sourceCell26
  | ⟨27,h⟩ => exact sourceCell27
  | ⟨28,h⟩ => exact sourceCell28
  | ⟨29,h⟩ => exact sourceCell29
  | ⟨30,h⟩ => exact sourceCell30
  | ⟨31,h⟩ => exact sourceCell31
  | ⟨32,h⟩ => exact sourceCell32
  | ⟨33,h⟩ => exact sourceCell33
  | ⟨34,h⟩ => exact sourceCell34
  | ⟨35,h⟩ => exact sourceCell35
  | ⟨36,h⟩ => exact sourceCell36
  | ⟨37,h⟩ => exact sourceCell37
  | ⟨38,h⟩ => exact sourceCell38
  | ⟨39,h⟩ => exact sourceCell39
  | ⟨40,h⟩ => exact sourceCell40
  | ⟨41,h⟩ => exact sourceCell41
  | ⟨42,h⟩ => exact sourceCell42
  | ⟨43,h⟩ => exact sourceCell43
  | ⟨44,h⟩ => exact sourceCell44
  | ⟨45,h⟩ => exact sourceCell45
  | ⟨46,h⟩ => exact sourceCell46
  | ⟨47,h⟩ => exact sourceCell47
  | ⟨48,h⟩ => exact sourceCell48
  | ⟨49,h⟩ => exact sourceCell49
  | ⟨50,h⟩ => exact sourceCell50
  | ⟨51,h⟩ => exact sourceCell51
  | ⟨52,h⟩ => exact sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

theorem upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12223 (gMinus 12223) (1 - (scalarRow12223.table i).lower) ≤ 1 ∧
    energyUpper 12223 (gMinus 12223) (BstLean.Part211.gPlus 12223)
      (finiteEnergy 12223 12223 0.011) (1 - (scalarRow12223.table i).lower) ≤ (scalarRow12223.table i).energy := by
  match i with
  | ⟨0,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨2,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨3,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨4,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨5,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨6,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨7,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨8,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨9,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨10,h⟩ => exact upperEnergy10
  | ⟨11,h⟩ => exact upperEnergy11
  | ⟨12,h⟩ => exact upperEnergy12
  | ⟨13,h⟩ => exact upperEnergy13
  | ⟨14,h⟩ => exact upperEnergy14
  | ⟨15,h⟩ => exact upperEnergy15
  | ⟨16,h⟩ => exact upperEnergy16
  | ⟨17,h⟩ => exact upperEnergy17
  | ⟨18,h⟩ => exact upperEnergy18
  | ⟨19,h⟩ => exact upperEnergy19
  | ⟨20,h⟩ => exact upperEnergy20
  | ⟨21,h⟩ => exact upperEnergy21
  | ⟨22,h⟩ => exact upperEnergy22
  | ⟨23,h⟩ => exact upperEnergy23
  | ⟨24,h⟩ => exact upperEnergy24
  | ⟨25,h⟩ => exact upperEnergy25
  | ⟨26,h⟩ => exact upperEnergy26
  | ⟨27,h⟩ => exact upperEnergy27
  | ⟨28,h⟩ => exact upperEnergy28
  | ⟨29,h⟩ => exact upperEnergy29
  | ⟨30,h⟩ => exact upperEnergy30
  | ⟨31,h⟩ => exact upperEnergy31
  | ⟨32,h⟩ => exact upperEnergy32
  | ⟨33,h⟩ => exact upperEnergy33
  | ⟨34,h⟩ => exact upperEnergy34
  | ⟨35,h⟩ => exact upperEnergy35
  | ⟨36,h⟩ => exact upperEnergy36
  | ⟨37,h⟩ => exact upperEnergy37
  | ⟨38,h⟩ => exact upperEnergy38
  | ⟨39,h⟩ => exact upperEnergy39
  | ⟨40,h⟩ => exact upperEnergy40
  | ⟨41,h⟩ => exact upperEnergy41
  | ⟨42,h⟩ => exact upperEnergy42
  | ⟨43,h⟩ => exact upperEnergy43
  | ⟨44,h⟩ => exact upperEnergy44
  | ⟨45,h⟩ => exact upperEnergy45
  | ⟨46,h⟩ => exact upperEnergy46
  | ⟨47,h⟩ => exact upperEnergy47
  | ⟨48,h⟩ => exact upperEnergy48
  | ⟨49,h⟩ => exact upperEnergy49
  | ⟨50,h⟩ => exact upperEnergy50
  | ⟨51,h⟩ => exact upperEnergy51
  | ⟨52,h⟩ => exact upperEnergy52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

noncomputable def sourceNumerics12223 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part277.CellSourceNumericsP 12223 (scalarRow12223.table i) scalarRow12223.M scalarRow12223.H scalarRow12223.xi
      1.22 1.12 1.25 0.665 0.47199 0.52358 := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part281.Groups.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := source_cell hi
  have E := upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := BstLean.Part277.centreCertificate_from_momentP (by norm_num)
      (pilot_groupMomentCertificate hg) hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
      (r := (110.557677254906 : ℝ)) (F := (0.008771 : ℝ))
      (by norm_num) (by norm_num) pilot_finite_centre_upper (by norm_num)
      (fun θ hθ => by
        convert (BstLean.Part281.energy_lower_data (by norm_num : 11883 ≤ 12223)
          ⟨hθ.1,hθ.2.trans G.window.2⟩).1 using 1 <;> norm_num)
    energy_allowance := scalarRow12223.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12223]
    centre_nonneg := (scalarRow12223.certificate i).centre_nonneg
    centre_upper := hc
    MP_nonneg := by norm_num
    e0_pos := by norm_num
    operator := by
      intro c τ hτ
      exact (BstLean.Part277.operator_allowance_11883
        (by norm_num : 11883 ≤ 12223) c hτ).trans (by norm_num)
    lower := fun θ hθ => by
      convert (BstLean.Part281.energy_lower_data
        (by norm_num : 11883 ≤ 12223) ⟨hθ.1,hθ.2.trans G.window.2⟩).2 using 1 <;> norm_num
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part281.Dir11883.direction_budget_11883 (by norm_num : 11883 ≤ 12223)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12223])
    source_lower := hl
    source_upper := hu
    source_upper_one := hu532.trans (by norm_num)
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }
end BstLean.Part281.N12223
