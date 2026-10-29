import BstLean.Part281FirstShardAudit
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
import BstLean.Part281EnergyLower
import BstLean.Part281Group9
import BstLean.Part281Groups
import BstLean.Part281SourceCommon
import BstLean.Part281TailBounds
import BstLean.Part281UniformEnergy
namespace BstLean.Part281.N12100
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211
theorem pilot_wn_upper : wn 12100 ≤ (1.036694214877 : ℝ) := by
  have hr : (110.000000000000 : ℝ) ≤ √(12100 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (110.000000000000 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : finiteEnergy 12100 12100 (11 / 1000) ≤ (0.008771 : ℝ) := by
  convert BstLean.Part277.finite_centre_11883 (by norm_num : 11883 ≤ 12100) using 1 <;> norm_num
noncomputable def pilotParallelCap : ℝ := BstLean.Part281.scalarRow12100.xi
end BstLean.Part281.N12100

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part281.N12100
open BstLean.Part253
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036694214876 : ℝ) ≤ wn 12100 := by
  have hn : √(12100 : ℝ) ≤ 110.000000000000 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12100 : ℝ) := by positivity
  have hd : (2 : ℝ) / 110.000000000000 ≤ 2 / √(12100 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000264596708 : ℝ) ≤ rhoBar 12100 csC ∧
    rhoBar 12100 csC ≤ 0.000264597117 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036694214876 : ℝ) / (1.295212 * 12100) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036694214877 : ℝ) / (1.29521 * 12100) := by gcongr
      _ ≤ (0.000264597117 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12100 csC) ≤ 0.001058458480 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12100 csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part281.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12100 csC) (piBar (rhoBar 12100 csC)) ≤ 0.000202101538 ∧
    cc1 (rhoBar 12100 csC) (piBar (rhoBar 12100 csC)) ≤ 0.000128598453 ∧
    cc2 (rhoBar 12100 csC) ≤ 0.000074652268 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12100 csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12100 csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12100 csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12100 csC * nuR (rhoBar 12100 csC)) ≤ 0.000529211737 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000264597117 : ℝ) * 0.001058458480 := by gcongr
      _ ≤ (0.000529211737 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12100 csC) * nuR (rhoBar 12100 csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001058458480 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12100 csC) * rhoBar 12100 csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000264597117 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000264597117 / 2 + 0.399 * 0.001058458480 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000202101538 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000529211737 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000128598453 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000264597117 / 1.414213562 := by gcongr
      _ ≤ (0.000074652268 : ℝ) := by norm_num

end BstLean.Part281.N12100

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part281.N12100
open BstLean.Part253
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12100 csC) (piBar (rhoBar 12100 csC)) ≤ 1.76390E-7 := by
  have hr0 : 0 ≤ rhoBar 12100 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12100 csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12100 csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12100 csC) (piBar (rhoBar 12100 csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12100 csC) (piBar (rhoBar 12100 csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12100 csC) := by unfold cc2; positivity
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
    _ ≤ (0.000202101538 : ℝ) ^ 2 + 0.000128598453 ^ 2 + 3 * 0.000074652268 ^ 2 +
        2 * 0.797885 * 0.000202101538 * 0.000128598453 + 2 * 0.000202101538 * 0.000074652268 +
        4 * 0.797885 * 0.000128598453 * 0.000074652268 := by gcongr
    _ ≤ (1.76390E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12100 csC Θ ≤ 0.002764395581 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12100 csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12100 csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12100 csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12100 csC) (piBar (rhoBar 12100 csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12100 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036694214877 * 1.76390E-7 / (0.000264596708 : ℝ) := by gcongr
    _ ≤ 0.002764395581 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12100 csC Θ ≤ 0.003069864367 + 0.000698515404 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12100 csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12100 csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12100 csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036694214877 : ℝ) * ((2 * Θ * 0.000264597117 +
        (6863 / 10000) * 0.000264597117 * 12100 * 0.001058458480) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.003069864367 + 0.000698515404 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09430 : ℝ) ≤ gap 2 (rhoBar 12100 csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997300 : ℝ) ≤ √(1 - 2 * rhoBar 12100 csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12100 0.011 Θ ∧ gammaRatio 12100 0.011 Θ ≤ 0.000090961647 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12100 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036694214877 : ℝ) * 0.525 / ((1 - 0.011) * 12100) := by gcongr
      _ ≤ (0.000090961647 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.05504 : ℝ) ≤ gap 1 (gammaRatio 12100 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.9999535 : ℝ) ≤ √(1 - gammaRatio 12100 0.011 Θ) :=
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
    badAllowance 12100 csC 0.011 1.22 1.12 Θ ≤ 0.001306319180 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12100 csC) 1.22 ≤ 5.0566E-8 := by
    have he : (16.8 : ℝ) ≤ gap 2 (rhoBar 12100 csC) 1.22 ^ 2 / (2 * rhoBar 12100 csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12100 csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part281.Tails.exp_minus_16_8_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12100 0.011 Θ) 1.12 ≤ 6.1761E-8 := by
    have he : (16.6 : ℝ) ≤ gap 1 (gammaRatio 12100 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12100 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12100 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part281.Tails.exp_minus_16_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12100 csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12100 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036694214877 : ℝ) * 12100 *
        (5.0566E-8 / 1.1045361 + 6.1761E-8 / 1.05830052) := by gcongr
    _ ≤ (0.001306319180 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12100 csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.004376183547 + 0.003462910985 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part281.N12100

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part281.N12100
open BstLean.Part253
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12100 csC) (piBar (rhoBar 12100 csC)) := by
  have hr0 : 0 ≤ rhoBar 12100 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12100 csC)
  have hv0 : 0 ≤ nuR (rhoBar 12100 csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12100 csC Θ := by
  have hr0 : 0 ≤ rhoBar 12100 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12100 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12100 csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12100 csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12100 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12100 csC)
  have hv0 : 0 ≤ nuR (rhoBar 12100 csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12100 csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12100 csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12100 csC 0.011 0.46 Θ ≤ 0.053784168379 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - csC * 0.46 / 2) / 12100) ≤ 0.010856705283 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12100 * Θ) ≤ 0.737742816170 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036694214877)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010856705283 + 2 * 0.737742816170 / 12100) := by gcongr
    _ ≤ (0.053784168379 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12100 12 ≤ 0.0016 := by
  have h5 : √(5 : ℝ) ≤ 2.236068 := sqrt_le_iff.mpr (by norm_num)
  have h12 : √(12 : ℝ) ≤ 3.464102 := sqrt_le_iff.mpr (by norm_num)
  have h1 : N12bar 12100 12 ≤ 0.000757377852 := by
    unfold N12bar
    simp only [Nat.cast_ofNat]
    linarith
  have h10 : 0 ≤ N12bar 12100 12 := by unfold N12bar; positivity
  unfold N22bar
  nlinarith

theorem pilot_radial_centre_bound {Θ T R : ℝ} (hΘ : 0 ≤ Θ) (hT : 0 ≤ T)
    (hTsq : 1.25 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0016 + T) / 110.000000000000 ≤ R) : xiNr 12100 Θ 1.25 ≤ R := by
  have hs : √((1.25 : ℝ) * Θ) ≤ T := sqrt_le_iff.mpr ⟨hT, hTsq⟩
  have hn := pilot_n22_upper
  have hn0 : 0 ≤ N22bar 12100 12 := by unfold N22bar N12bar; positivity
  have hN : (110.000000000000 : ℝ) ≤ √(12100 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold xiNr
  simp only [Nat.cast_ofNat]
  apply le_trans ?_ hR
  gcongr
  linarith

theorem pilot_full_formula_bound {Θ S X T R B : ℝ}
    (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hXsq : 0.2654 * S + 0.004376183547 + 0.003462910985 * Θ ≤ X ^ 2)
    (hT : 0 ≤ T) (hTsq : 1.25 * Θ ≤ T ^ 2)
    (hR : (Θ * 1.0016 + T) / 110.000000000000 ≤ R)
    (hB : (X + 0.053784168379 + R + 0.008771) ^ 2 ≤ B) :
    fullFormula 12100 12100 0.011 1.22 1.12 0.46 Θ S 1.25 ≤ B := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hm : √(momentAllowance 12100 csC 0.011 1.22 1.12 Θ S) ≤ X :=
    sqrt_le_iff.mpr ⟨hX, (pilot_moment_upper hw hS).trans hXsq⟩
  have hd := pilot_deviation_upper hΘ hw.2
  have hr := pilot_radial_centre_bound hΘ hT hTsq hR
  have hf : finiteEnergy 12100 12100 0.011 ≤ 0.008771 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hd0 : 0 ≤ sharpDeviation 12100 csC 0.011 0.46 Θ := by unfold sharpDeviation; positivity
  have hn0 : 0 ≤ N22bar 12100 12 := by unfold N22bar N12bar; positivity
  have hr0 : 0 ≤ xiNr 12100 Θ 1.25 := by unfold xiNr; positivity
  have hf0 := finiteEnergy_nonneg 12100 12100 (by norm_num : (0 : ℝ) ≤ 0.011)
  unfold fullFormula
  apply le_trans ?_ hB
  gcongr

end BstLean.Part281.N12100

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part281.N12100
open BstLean.Part253
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560475089033 : ℝ) ≤ plow 12100 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12100) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053780431815)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001451307681) : eMP 12100 0.011 xi bn ≤ 0.001248626526 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12100 : ℝ) * (1 - 0.011))) ≤ 0.000617253948 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001451307681 / (12100 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000617253948 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000617253948 : ℝ) + 3.141593 * 0.053780431815 / (12100 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001248626526 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053780431815)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001451307681) : PiBarMP 12100 12 0.011 xi bn ≤ 0.165244102380 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12100 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.038096032353 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (109.393327035976 : ℝ) ≤ √((12100 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (110.000000000000 : ℝ) ≤ √(12100 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12100) ≤ 0.126658256935 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.038096032353 + 0.053780431815 * 1.772454 / (2 * (109.393327035976 : ℝ))) * (1 + 0.001248626526) +
        8 / (12100 * 110.000000000000) + 0.126658256935 := by gcongr
    _ ≤ (0.165244102380 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053780431815)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001451307681) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.285690252420) :
    parallelOracle 12100 0.011 xi bn cd ≤ 0.166288894170 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12100 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12100 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560475089033 : ℝ) ≤ plow 12100 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.000000000000 : ℝ) ≤ √(12100 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.285690252420 : ℝ) / (2 * 0.560475089033 * 110.000000000000)) * 0.165244102380 +
        0.285690252420 ^ 2 / (2 * 0.560475089033 * 110.000000000000) := by gcongr
    _ ≤ (0.166288894170 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053780431815) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001451307681)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.285690252420) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12100 12100 0.011 xi bn cd Θ 1.25 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560475089033 : ℝ) ≤ plow 12100 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (110.000000000000 : ℝ) ≤ √(12100 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12100 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.25 : ℝ) * Θ) ≤ 0.810092587301 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12100 Θ 1.25 ≤ 0.012144841703 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0016 + 0.810092587301) / 110.000000000000 := by gcongr <;> linarith
      _ ≤ (0.012144841703 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12100 Θ 1.25 := by unfold xiNr; positivity
  have hf : finiteEnergy 12100 12100 0.011 ≤ 0.008771 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12100 12100 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12100 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12100 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12100 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12100 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.166288894170 + 0.012144841703 + (0.008771 : ℝ) *
        (1 + 2 * (0.285690252420 + 0.012144841703) / (0.560475089033 * 110.000000000000))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part281.scalarRow12100]

end BstLean.Part281.N12100

/-! The original eight local profiles supply actual 12100 moment certificates. -/
namespace BstLean.Part281.N12100
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part281.Groups

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : BstLean.Part281.Groups.NeededGroup g) :
    MomentCertificate 12100 0.011 1.22 1.12 0.46 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g)
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
    0 ≤ momentAllowance 12100 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g) ∧
    momentAllowance 12100 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g) ≤ 0.053780431815 ∧
    0 ≤ bN 12100 csC (BstLean.Part281.Groups.groupTheta g) ∧ bN 12100 csC (BstLean.Part281.Groups.groupTheta g) ≤ 0.001451307681 := by
  have G := BstLean.Part281.Groups.group_scalar hg
  have hΘ : 0 ≤ BstLean.Part281.Groups.groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : BstLean.Part281.Groups.NeededGroup g) :
    parallelFormula 12100 12100 0.011
      (momentAllowance 12100 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g))
      (bN 12100 csC (BstLean.Part281.Groups.groupTheta g))
      (√(momentAllowance 12100 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g)) +
        sharpDeviation 12100 csC 0.011 0.46 (BstLean.Part281.Groups.groupTheta g)) (BstLean.Part281.Groups.groupTheta g) 1.25 ≤ pilotParallelCap := by
  have G := BstLean.Part281.Groups.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ BstLean.Part281.Groups.groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12100 csC 0.011 0.46 (BstLean.Part281.Groups.groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12100 csC 0.011 1.22 1.12
      (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g)) ≤ 0.231906084041 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : BstLean.Part281.Groups.NeededGroup g) :
    eMP 12100 0.011
      (momentAllowance 12100 csC 0.011 1.22 1.12 (BstLean.Part281.Groups.groupTheta g) (BstLean.Part281.Groups.groupProfile g))
      (bN 12100 csC (BstLean.Part281.Groups.groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part281.N12100
namespace BstLean.Part281.N12100
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.087543076426
  | 2 => 0.088529350899
  | 3 => 0.089520926628
  | 4 => 0.090520789868
  | 5 => 0.091532486546
  | 6 => 0.092560196356
  | 7 => 0.093608812264
  | 8 => 0.094684025220
  | _ => 0

theorem pilot_fullGroup1 :
    fullFormula 12100 12100 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 1) (BstLean.Part281.Groups.groupProfile 1) 1.25 ≤ pilotGroupCentre 1 := by
  apply pilot_full_formula_bound (X := (0.221356401114 : ℝ)) (T := (0.770098081416 : ℝ)) (R := (0.011320891189 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup2 :
    fullFormula 12100 12100 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 2) (BstLean.Part281.Groups.groupProfile 2) 1.25 ≤ pilotGroupCentre 2 := by
  apply pilot_full_formula_bound (X := (0.222920635400 : ℝ)) (T := (0.775935939689 : ℝ)) (R := (0.011439707852 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup3 :
    fullFormula 12100 12100 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 3) (BstLean.Part281.Groups.groupProfile 3) 1.25 ≤ pilotGroupCentre 3 := by
  apply pilot_full_formula_bound (X := (0.224464579936 : ℝ)) (T := (0.781730202020 : ℝ)) (R := (0.011558128180 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup4 :
    fullFormula 12100 12100 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 4) (BstLean.Part281.Groups.groupProfile 4) 1.25 ≤ pilotGroupCentre 4 := by
  apply pilot_full_formula_bound (X := (0.225988433782 : ℝ)) (T := (0.787481832331 : ℝ)) (R := (0.011676160952 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup5 :
    fullFormula 12100 12100 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 5) (BstLean.Part281.Groups.groupProfile 5) 1.25 ≤ pilotGroupCentre 5 := by
  apply pilot_full_formula_bound (X := (0.227492389795 : ℝ)) (T := (0.793191757238 : ℝ)) (R := (0.011793814585 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup6 :
    fullFormula 12100 12100 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 6) (BstLean.Part281.Groups.groupProfile 6) 1.25 ≤ pilotGroupCentre 6 := by
  apply pilot_full_formula_bound (X := (0.228976635462 : ℝ)) (T := (0.798860870240 : ℝ)) (R := (0.011911097191 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup7 :
    fullFormula 12100 12100 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 7) (BstLean.Part281.Groups.groupProfile 7) 1.25 ≤ pilotGroupCentre 7 := by
  apply pilot_full_formula_bound (X := (0.230441353672 : ℝ)) (T := (0.804490035675 : ℝ)) (R := (0.012028016647 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_fullGroup8 :
    fullFormula 12100 12100 0.011 1.22 1.12 0.46
      (BstLean.Part281.Groups.groupTheta 8) (BstLean.Part281.Groups.groupProfile 8) 1.25 ≤ pilotGroupCentre 8 := by
  apply pilot_full_formula_bound (X := (0.231886721655 : ℝ)) (T := (0.810080085548 : ℝ)) (R := (0.012144580506 : ℝ))
  all_goals norm_num [BstLean.Part281.Groups.groupTheta,BstLean.Part281.Groups.groupProfile,pilotGroupCentre]

theorem pilot_group_full {g : Fin 10} (hg : BstLean.Part281.Groups.NeededGroup g) :
    fullFormula 12100 12100 0.011 1.22 1.12 0.46
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
end BstLean.Part281.N12100
