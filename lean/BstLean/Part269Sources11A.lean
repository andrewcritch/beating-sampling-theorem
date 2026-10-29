import BstLean.Part269TailBounds
import BstLean.Part211Full
import BstLean.Part211MA
import BstLean.Part211Parallel
import BstLean.Part253CentreConstants
import BstLean.Part253CentreFormula
import BstLean.Part253CentreTerms
import BstLean.Part253Data
import BstLean.Part253EnergyUpper
import BstLean.Part253Exp
import BstLean.Part253ExpFraction
import BstLean.Part253FiniteCentre
import BstLean.Part253GroupBounds
import BstLean.Part263Coverage
import BstLean.Part264Centre
import BstLean.Part264EnergyLower
import BstLean.Part264HS
import BstLean.Part264Source
import BstLean.Part264bSourceCommon
import BstLean.Part269Direction11
import BstLean.Part269Shared11
import BstLean.Part269Finite
import BstLean.Part269Rows11
import BstLean.Part269Source
/-! Actual 12625 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12625
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12625 ≤ (1.035916364443 : ℝ) := by
  have hr : (112.361025271221 : ℝ) ≤ √(12625 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.361025271221 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12625 12625 (11 / 1000) ≤
    (0.008507283096 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12625) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.361025271221 : ℝ) ≤ √(12625 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12625)
  have hdiv : K / √(12625 : ℝ) ≤ K / 112.361025271221 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.361025271221 ≤ (0.008507283096 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12625.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12625 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12625 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12625 := gPlus_lower 12625
end BstLean.Part269.N12625

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12625
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035916364442 : ℝ) ≤ wn 12625 := by
  have hn : √(12625 : ℝ) ≤ 112.361025271222 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12625 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.361025271222 ≤ 2 / √(12625 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253403400 : ℝ) ≤ rhoBar 12625 BstLean.Part154.csC ∧
    rhoBar 12625 BstLean.Part154.csC ≤ 0.000253403792 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035916364442 : ℝ) / (1.295212 * 12625) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035916364443 : ℝ) / (1.29521 * 12625) := by gcongr
      _ ≤ (0.000253403792 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12625 BstLean.Part154.csC) ≤ 0.001013679382 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12625 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12625 BstLean.Part154.csC) (piBar (rhoBar 12625 BstLean.Part154.csC)) ≤ 0.000193551580 ∧
    cc1 (rhoBar 12625 BstLean.Part154.csC) (piBar (rhoBar 12625 BstLean.Part154.csC)) ≤ 0.000123158145 ∧
    cc2 (rhoBar 12625 BstLean.Part154.csC) ≤ 0.000071494233 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12625 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12625 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12625 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12625 BstLean.Part154.csC * nuR (rhoBar 12625 BstLean.Part154.csC)) ≤ 0.000506823638 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253403792 : ℝ) * 0.001013679382 := by gcongr
      _ ≤ (0.000506823638 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12625 BstLean.Part154.csC) * nuR (rhoBar 12625 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001013679382 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12625 BstLean.Part154.csC) * rhoBar 12625 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253403792 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253403792 / 2 + 0.399 * 0.001013679382 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193551580 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506823638 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123158145 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253403792 / 1.414213562 := by gcongr
      _ ≤ (0.000071494233 : ℝ) := by norm_num

end BstLean.Part269.N12625

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12625
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12625 BstLean.Part154.csC) (piBar (rhoBar 12625 BstLean.Part154.csC)) ≤ 1.61781E-7 := by
  have hr0 : 0 ≤ rhoBar 12625 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12625 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12625 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12625 BstLean.Part154.csC) (piBar (rhoBar 12625 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12625 BstLean.Part154.csC) (piBar (rhoBar 12625 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12625 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193551580 : ℝ) ^ 2 + 0.000123158145 ^ 2 + 3 * 0.000071494233 ^ 2 +
        2 * 0.797885 * 0.000193551580 * 0.000123158145 + 2 * 0.000193551580 * 0.000071494233 +
        4 * 0.797885 * 0.000123158145 * 0.000071494233 := by gcongr
    _ ≤ (1.61781E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12625 BstLean.Part154.csC Θ ≤ 0.002645451251 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12625 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12625 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12625 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12625 BstLean.Part154.csC) (piBar (rhoBar 12625 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12625 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035916364443 * 1.61781E-7 / (0.000253403400 : ℝ) := by gcongr
    _ ≤ 0.002645451251 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12625 BstLean.Part154.csC Θ ≤ 0.002935580614 + 0.000668463977 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12625 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12625 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12625 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035916364443 : ℝ) * ((2 * Θ * 0.000253403792 +
        (6863 / 10000) * 0.000253403792 * 12625 * 0.001013679382) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002935580614 + 0.000668463977 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12625 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12625 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12625 0.011 Θ ∧ gammaRatio 12625 0.011 Θ ≤ 0.000087113671 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12625 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035916364443 : ℝ) * 0.525 / ((1 - 0.011) * 12625) := by gcongr
      _ ≤ (0.000087113671 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12625 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12625 0.011 Θ) :=
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
    badAllowance 12625 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12625 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12625 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12625 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12625 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12625 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12625 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12625 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12625 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12625 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12625 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035916364443 : ℝ) * 12625 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12625 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003612287085 + 0.003313915228 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12625

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12625
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12625 BstLean.Part154.csC) (piBar (rhoBar 12625 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12625 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12625 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12625 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12625 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12625 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12625 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12625 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12625 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12625 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12625 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12625 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12625 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12625 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12625 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052641668890 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12625) ≤ 0.010628574973 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12625 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035916364443)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010628574973 + 2 * 0.737676 / 12625) := by gcongr
    _ ≤ (0.052641668890 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12625 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12625

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12625
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500156419 : ℝ) ≤ plow 12625 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12625) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052858692580)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388861907) : eMP 12625 0.011 xi bn ≤ 0.001195580439 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12625 : ℝ) * (1 - 0.011))) ≤ 0.000591140418 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001388861907 / (12625 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591140418 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591140418 : ℝ) + 3.141593 * 0.052858692580 / (12625 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001195580439 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052858692580)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388861907) : PiBarMP 12625 12 0.011 xi bn ≤ 0.161734166052 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12625 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037267437624 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.741330759929 : ℝ) ≤ √((12625 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.361025271221 : ℝ) ≤ √(12625 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12625) ≤ 0.123996806092 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037267437624 + 0.052858692580 * 1.772454 / (2 * (111.741330759929 : ℝ))) * (1 + 0.001195580439) +
        8 / (12625 * 112.361025271221) + 0.123996806092 := by gcongr
    _ ≤ (0.161734166052 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052858692580)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388861907) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282551852614) :
    parallelOracle 12625 0.011 xi bn cd ≤ 0.162730808497 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12625 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12625 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500156419 : ℝ) ≤ plow 12625 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.361025271221 : ℝ) ≤ √(12625 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282551852614 : ℝ) / (2 * 0.560500156419 * 112.361025271221)) * 0.161734166052 +
        0.282551852614 ^ 2 / (2 * 0.560500156419 * 112.361025271221) := by gcongr
    _ ≤ (0.162730808497 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052858692580) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388861907)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282551852614) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12625 12625 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500156419 : ℝ) ≤ plow 12625 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.361025271221 : ℝ) ≤ √(12625 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12625 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12625 Θ 1.22 ≤ 0.011802139548 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.361025271221 := by gcongr <;> linarith
      _ ≤ (0.011802139548 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12625 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12625 12625 0.011 ≤ 0.008507283096 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12625 12625 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12625 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12625 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12625 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12625 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162730808497 + 0.011802139548 + (0.008507283096 : ℝ) *
        (1 + 2 * (0.282551852614 + 0.011802139548) / (0.560500156419 * 112.361025271221))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12625]

end BstLean.Part269.N12625

/-! The original eight local profiles supply actual 12625 moment certificates. -/
namespace BstLean.Part269.N12625
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12625 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part253.group_scalar hg
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
      exact (mul_le_mul_of_nonneg_right (hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part253.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : NeededGroup g) :
    0 ≤ momentAllowance 12625 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12625 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052858692580 ∧
    0 ≤ bN 12625 BstLean.Part154.csC (groupTheta g) ∧ bN 12625 BstLean.Part154.csC (groupTheta g) ≤ 0.001388861907 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12625 12625 0.011
      (momentAllowance 12625 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12625 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12625 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12625 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12625 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12625 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229910183724 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12625 0.011
      (momentAllowance 12625 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12625 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12625
/-! The actual computed-centre upper energy formula at 12625. -/
namespace BstLean.Part269.N12625
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12625

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12625
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12625)
open BstLean.Part268 (cell12625)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085712105998
  | 2 => 0.086659002946
  | 3 => 0.087604656109
  | 4 => 0.088550624749
  | 5 => 0.089498790068
  | 6 => 0.090451402401
  | 7 => 0.091411132729
  | 8 => 0.092381128539
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12625 12625 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12625 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12625

/-! Actual upper energy certificates on all 43 source endpoints at 12625. -/
namespace BstLean.Part269.N12625
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12625)
open BstLean.Part268 (cell12625)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12625 (gMinus 12625) (1 - (cell12625 i).lower) ≤ 1 ∧
    energyUpper 12625 (gMinus 12625) (BstLean.Part211.gPlus 12625)
      (finiteEnergy 12625 12625 0.011) (1 - (cell12625 i).lower) ≤
      (cell12625 i).energy := by
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
  | ⟨10,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨10,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨11,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨12,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨13,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨14,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨15,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨16,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨17,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨18,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨19,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨20,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨21,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨22,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨23,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨24,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨25,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨26,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨27,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨28,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨29,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨30,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨31,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨32,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨33,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨34,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨35,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨36,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨37,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨38,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨39,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨40,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨41,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨42,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨43,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨44,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨45,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨46,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨47,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨48,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨49,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨50,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨51,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12625) (by norm_num)
        (q := 1 - (cell12625 ⟨52,by decide⟩).lower)
        (by norm_num [cell12625]) (by norm_num [cell12625])
      exact ⟨E.1,E.2.trans (by norm_num [cell12625])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12625

/-! Source-cell containment and simple scalar guards at 12625. -/
namespace BstLean.Part269.N12625
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12625)
open BstLean.Part268 (cell12625)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12625 ⟨10,by decide⟩).lower ∧ (cell12625 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12625 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12625 ⟨11,by decide⟩).lower ∧ (cell12625 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12625 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12625 ⟨12,by decide⟩).lower ∧ (cell12625 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12625 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12625 ⟨13,by decide⟩).lower ∧ (cell12625 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12625 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12625 ⟨14,by decide⟩).lower ∧ (cell12625 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12625 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12625 ⟨15,by decide⟩).lower ∧ (cell12625 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12625 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12625 ⟨16,by decide⟩).lower ∧ (cell12625 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12625 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12625 ⟨17,by decide⟩).lower ∧ (cell12625 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12625 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12625 ⟨18,by decide⟩).lower ∧ (cell12625 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12625 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12625 ⟨19,by decide⟩).lower ∧ (cell12625 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12625 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12625 ⟨20,by decide⟩).lower ∧ (cell12625 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12625 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12625 ⟨21,by decide⟩).lower ∧ (cell12625 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12625 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12625 ⟨22,by decide⟩).lower ∧ (cell12625 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12625 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12625 ⟨23,by decide⟩).lower ∧ (cell12625 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12625 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12625 ⟨24,by decide⟩).lower ∧ (cell12625 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12625 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12625 ⟨25,by decide⟩).lower ∧ (cell12625 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12625 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12625 ⟨26,by decide⟩).lower ∧ (cell12625 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12625 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12625 ⟨27,by decide⟩).lower ∧ (cell12625 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12625 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12625 ⟨28,by decide⟩).lower ∧ (cell12625 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12625 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12625 ⟨29,by decide⟩).lower ∧ (cell12625 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12625 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12625 ⟨30,by decide⟩).lower ∧ (cell12625 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12625 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12625 ⟨31,by decide⟩).lower ∧ (cell12625 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12625 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12625 ⟨32,by decide⟩).lower ∧ (cell12625 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12625 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12625 ⟨33,by decide⟩).lower ∧ (cell12625 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12625 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12625 ⟨34,by decide⟩).lower ∧ (cell12625 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12625 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12625 ⟨35,by decide⟩).lower ∧ (cell12625 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12625 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12625 ⟨36,by decide⟩).lower ∧ (cell12625 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12625 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12625 ⟨37,by decide⟩).lower ∧ (cell12625 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12625 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12625 ⟨38,by decide⟩).lower ∧ (cell12625 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12625 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12625 ⟨39,by decide⟩).lower ∧ (cell12625 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12625 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12625 ⟨40,by decide⟩).lower ∧ (cell12625 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12625 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12625 ⟨41,by decide⟩).lower ∧ (cell12625 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12625 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12625 ⟨42,by decide⟩).lower ∧ (cell12625 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12625 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12625 ⟨43,by decide⟩).lower ∧ (cell12625 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12625 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12625 ⟨44,by decide⟩).lower ∧ (cell12625 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12625 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12625 ⟨45,by decide⟩).lower ∧ (cell12625 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12625 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12625 ⟨46,by decide⟩).lower ∧ (cell12625 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12625 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12625 ⟨47,by decide⟩).lower ∧ (cell12625 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12625 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12625 ⟨48,by decide⟩).lower ∧ (cell12625 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12625 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12625 ⟨49,by decide⟩).lower ∧ (cell12625 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12625 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12625 ⟨50,by decide⟩).lower ∧ (cell12625 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12625 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12625 ⟨51,by decide⟩).lower ∧ (cell12625 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12625 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12625 ⟨52,by decide⟩).lower ∧ (cell12625 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12625 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12625 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12625 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12625,cell12625,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12625 i).lower ∧
    (cell12625 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12625 i).upper ≤ (0.532 : ℝ) ∧
    (cell12625 i).centre ≤ (0.1 : ℝ) ∧ (cell12625 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12625 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12625 i).centre = pilotGroupCentre (centreGroup i) := by
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
  | ⟨10,h⟩ => exact pilot_sourceCell10
  | ⟨11,h⟩ => exact pilot_sourceCell11
  | ⟨12,h⟩ => exact pilot_sourceCell12
  | ⟨13,h⟩ => exact pilot_sourceCell13
  | ⟨14,h⟩ => exact pilot_sourceCell14
  | ⟨15,h⟩ => exact pilot_sourceCell15
  | ⟨16,h⟩ => exact pilot_sourceCell16
  | ⟨17,h⟩ => exact pilot_sourceCell17
  | ⟨18,h⟩ => exact pilot_sourceCell18
  | ⟨19,h⟩ => exact pilot_sourceCell19
  | ⟨20,h⟩ => exact pilot_sourceCell20
  | ⟨21,h⟩ => exact pilot_sourceCell21
  | ⟨22,h⟩ => exact pilot_sourceCell22
  | ⟨23,h⟩ => exact pilot_sourceCell23
  | ⟨24,h⟩ => exact pilot_sourceCell24
  | ⟨25,h⟩ => exact pilot_sourceCell25
  | ⟨26,h⟩ => exact pilot_sourceCell26
  | ⟨27,h⟩ => exact pilot_sourceCell27
  | ⟨28,h⟩ => exact pilot_sourceCell28
  | ⟨29,h⟩ => exact pilot_sourceCell29
  | ⟨30,h⟩ => exact pilot_sourceCell30
  | ⟨31,h⟩ => exact pilot_sourceCell31
  | ⟨32,h⟩ => exact pilot_sourceCell32
  | ⟨33,h⟩ => exact pilot_sourceCell33
  | ⟨34,h⟩ => exact pilot_sourceCell34
  | ⟨35,h⟩ => exact pilot_sourceCell35
  | ⟨36,h⟩ => exact pilot_sourceCell36
  | ⟨37,h⟩ => exact pilot_sourceCell37
  | ⟨38,h⟩ => exact pilot_sourceCell38
  | ⟨39,h⟩ => exact pilot_sourceCell39
  | ⟨40,h⟩ => exact pilot_sourceCell40
  | ⟨41,h⟩ => exact pilot_sourceCell41
  | ⟨42,h⟩ => exact pilot_sourceCell42
  | ⟨43,h⟩ => exact pilot_sourceCell43
  | ⟨44,h⟩ => exact pilot_sourceCell44
  | ⟨45,h⟩ => exact pilot_sourceCell45
  | ⟨46,h⟩ => exact pilot_sourceCell46
  | ⟨47,h⟩ => exact pilot_sourceCell47
  | ⟨48,h⟩ => exact pilot_sourceCell48
  | ⟨49,h⟩ => exact pilot_sourceCell49
  | ⟨50,h⟩ => exact pilot_sourceCell50
  | ⟨51,h⟩ => exact pilot_sourceCell51
  | ⟨52,h⟩ => exact pilot_sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12625

/-! The local source numeric instances at 12625 have no network premises. -/
namespace BstLean.Part269.N12625
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12625)
open BstLean.Part268 (cell12625)

noncomputable def sourceNumerics12625 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12625 (cell12625 i)
      scalarRow12625.M scalarRow12625.H scalarRow12625.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := pilot_source_cell hi
  have E := pilot_upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := centreCertificate_from_moment (by norm_num)
      (G.window.2.trans (by norm_num)) (pilot_groupMomentCertificate hg)
      hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
    energy_allowance := scalarRow12625.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12625]
    centre_nonneg := (scalarRow12625.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12625])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12625
/-! Actual 12626 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12626
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12626 ≤ (1.035914929551 : ℝ) := by
  have hr : (112.365475124701 : ℝ) ≤ √(12626 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.365475124701 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12626 12626 (11 / 1000) ≤
    (0.008506946191 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12626) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.365475124701 : ℝ) ≤ √(12626 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12626)
  have hdiv : K / √(12626 : ℝ) ≤ K / 112.365475124701 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.365475124701 ≤ (0.008506946191 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12626.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12626 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12626 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12626 := gPlus_lower 12626
end BstLean.Part269.N12626

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12626
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035914929550 : ℝ) ≤ wn 12626 := by
  have hn : √(12626 : ℝ) ≤ 112.365475124702 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12626 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.365475124702 ≤ 2 / √(12626 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253382979 : ℝ) ≤ rhoBar 12626 BstLean.Part154.csC ∧
    rhoBar 12626 BstLean.Part154.csC ≤ 0.000253383371 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035914929550 : ℝ) / (1.295212 * 12626) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035914929551 : ℝ) / (1.29521 * 12626) := by gcongr
      _ ≤ (0.000253383371 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12626 BstLean.Part154.csC) ≤ 0.001013597688 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12626 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12626 BstLean.Part154.csC) (piBar (rhoBar 12626 BstLean.Part154.csC)) ≤ 0.000193535982 ∧
    cc1 (rhoBar 12626 BstLean.Part154.csC) (piBar (rhoBar 12626 BstLean.Part154.csC)) ≤ 0.000123148219 ∧
    cc2 (rhoBar 12626 BstLean.Part154.csC) ≤ 0.000071488471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12626 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12626 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12626 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12626 BstLean.Part154.csC * nuR (rhoBar 12626 BstLean.Part154.csC)) ≤ 0.000506782793 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253383371 : ℝ) * 0.001013597688 := by gcongr
      _ ≤ (0.000506782793 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12626 BstLean.Part154.csC) * nuR (rhoBar 12626 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001013597688 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12626 BstLean.Part154.csC) * rhoBar 12626 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253383371 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253383371 / 2 + 0.399 * 0.001013597688 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193535982 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506782793 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123148219 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253383371 / 1.414213562 := by gcongr
      _ ≤ (0.000071488471 : ℝ) := by norm_num

end BstLean.Part269.N12626

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12626
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12626 BstLean.Part154.csC) (piBar (rhoBar 12626 BstLean.Part154.csC)) ≤ 1.61755E-7 := by
  have hr0 : 0 ≤ rhoBar 12626 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12626 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12626 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12626 BstLean.Part154.csC) (piBar (rhoBar 12626 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12626 BstLean.Part154.csC) (piBar (rhoBar 12626 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12626 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193535982 : ℝ) ^ 2 + 0.000123148219 ^ 2 + 3 * 0.000071488471 ^ 2 +
        2 * 0.797885 * 0.000193535982 * 0.000123148219 + 2 * 0.000193535982 * 0.000071488471 +
        4 * 0.797885 * 0.000123148219 * 0.000071488471 := by gcongr
    _ ≤ (1.61755E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12626 BstLean.Part154.csC Θ ≤ 0.002645235605 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12626 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12626 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12626 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12626 BstLean.Part154.csC) (piBar (rhoBar 12626 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12626 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035914929551 * 1.61755E-7 / (0.000253382979 : ℝ) := by gcongr
    _ ≤ 0.002645235605 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12626 BstLean.Part154.csC Θ ≤ 0.002935335899 + 0.000668409181 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12626 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12626 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12626 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035914929551 : ℝ) * ((2 * Θ * 0.000253383371 +
        (6863 / 10000) * 0.000253383371 * 12626 * 0.001013597688) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002935335899 + 0.000668409181 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12626 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12626 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12626 0.011 Θ ∧ gammaRatio 12626 0.011 Θ ≤ 0.000087106651 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12626 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035914929551 : ℝ) * 0.525 / ((1 - 0.011) * 12626) := by gcongr
      _ ≤ (0.000087106651 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12626 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12626 0.011 Θ) :=
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
    badAllowance 12626 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12626 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12626 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12626 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12626 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12626 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12626 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12626 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12626 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12626 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12626 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035914929551 : ℝ) * 12626 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12626 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003612042370 + 0.003313644786 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12626

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12626
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12626 BstLean.Part154.csC) (piBar (rhoBar 12626 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12626 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12626 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12626 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12626 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12626 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12626 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12626 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12626 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12626 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12626 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12626 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12626 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12626 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12626 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052639561523 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12626) ≤ 0.010628154064 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12626 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035914929551)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010628154064 + 2 * 0.737676 / 12626) := by gcongr
    _ ≤ (0.052639561523 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12626 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12626

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12626
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500202178 : ℝ) ≤ plow 12626 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12626) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052858305883)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388748693) : eMP 12626 0.011 xi bn ≤ 0.001195484282 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12626 : ℝ) * (1 - 0.011))) ≤ 0.000591092915 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001388748693 / (12626 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591092915 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591092915 : ℝ) + 3.141593 * 0.052858305883 / (12626 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001195484282 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052858305883)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388748693) : PiBarMP 12626 12 0.011 xi bn ≤ 0.161727710806 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12626 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037265918653 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.745756071539 : ℝ) ≤ √((12626 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.365475124701 : ℝ) ≤ √(12626 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12626) ≤ 0.123991895619 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037265918653 + 0.052858305883 * 1.772454 / (2 * (111.745756071539 : ℝ))) * (1 + 0.001195484282) +
        8 / (12626 * 112.365475124701) + 0.123991895619 := by gcongr
    _ ≤ (0.161727710806 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052858305883)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388748693) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282548904272) :
    parallelOracle 12626 0.011 xi bn cd ≤ 0.162724282208 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12626 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12626 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500202178 : ℝ) ≤ plow 12626 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.365475124701 : ℝ) ≤ √(12626 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282548904272 : ℝ) / (2 * 0.560500202178 * 112.365475124701)) * 0.161727710806 +
        0.282548904272 ^ 2 / (2 * 0.560500202178 * 112.365475124701) := by gcongr
    _ ≤ (0.162724282208 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052858305883) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388748693)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282548904272) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12626 12626 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500202178 : ℝ) ≤ plow 12626 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.365475124701 : ℝ) ≤ √(12626 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12626 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12626 Θ 1.22 ≤ 0.011801672165 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.365475124701 := by gcongr <;> linarith
      _ ≤ (0.011801672165 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12626 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12626 12626 0.011 ≤ 0.008506946191 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12626 12626 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12626 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12626 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12626 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12626 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162724282208 + 0.011801672165 + (0.008506946191 : ℝ) *
        (1 + 2 * (0.282548904272 + 0.011801672165) / (0.560500202178 * 112.365475124701))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12626]

end BstLean.Part269.N12626

/-! The original eight local profiles supply actual 12626 moment certificates. -/
namespace BstLean.Part269.N12626
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12626 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part253.group_scalar hg
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
      exact (mul_le_mul_of_nonneg_right (hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part253.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : NeededGroup g) :
    0 ≤ momentAllowance 12626 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12626 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052858305883 ∧
    0 ≤ bN 12626 BstLean.Part154.csC (groupTheta g) ∧ bN 12626 BstLean.Part154.csC (groupTheta g) ≤ 0.001388748693 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12626 12626 0.011
      (momentAllowance 12626 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12626 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12626 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12626 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12626 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12626 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229909342749 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12626 0.011
      (momentAllowance 12626 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12626 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12626
/-! The actual computed-centre upper energy formula at 12626. -/
namespace BstLean.Part269.N12626
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12626

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12626
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12626)
open BstLean.Part268 (cell12626)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085709105803
  | 2 => 0.086655945691
  | 3 => 0.087601533162
  | 4 => 0.088547425510
  | 5 => 0.089495501630
  | 6 => 0.090448009160
  | 7 => 0.091407615959
  | 8 => 0.092377465917
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12626 12626 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12626 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12626

/-! Actual upper energy certificates on all 43 source endpoints at 12626. -/
namespace BstLean.Part269.N12626
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12626)
open BstLean.Part268 (cell12626)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12626 (gMinus 12626) (1 - (cell12626 i).lower) ≤ 1 ∧
    energyUpper 12626 (gMinus 12626) (BstLean.Part211.gPlus 12626)
      (finiteEnergy 12626 12626 0.011) (1 - (cell12626 i).lower) ≤
      (cell12626 i).energy := by
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
  | ⟨10,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨10,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨11,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨12,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨13,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨14,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨15,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨16,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨17,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨18,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨19,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨20,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨21,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨22,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨23,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨24,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨25,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨26,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨27,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨28,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨29,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨30,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨31,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨32,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨33,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨34,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨35,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨36,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨37,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨38,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨39,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨40,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨41,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨42,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨43,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨44,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨45,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨46,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨47,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨48,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨49,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨50,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨51,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12626) (by norm_num)
        (q := 1 - (cell12626 ⟨52,by decide⟩).lower)
        (by norm_num [cell12626]) (by norm_num [cell12626])
      exact ⟨E.1,E.2.trans (by norm_num [cell12626])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12626

/-! Source-cell containment and simple scalar guards at 12626. -/
namespace BstLean.Part269.N12626
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12626)
open BstLean.Part268 (cell12626)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12626 ⟨10,by decide⟩).lower ∧ (cell12626 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12626 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12626 ⟨11,by decide⟩).lower ∧ (cell12626 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12626 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12626 ⟨12,by decide⟩).lower ∧ (cell12626 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12626 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12626 ⟨13,by decide⟩).lower ∧ (cell12626 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12626 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12626 ⟨14,by decide⟩).lower ∧ (cell12626 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12626 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12626 ⟨15,by decide⟩).lower ∧ (cell12626 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12626 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12626 ⟨16,by decide⟩).lower ∧ (cell12626 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12626 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12626 ⟨17,by decide⟩).lower ∧ (cell12626 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12626 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12626 ⟨18,by decide⟩).lower ∧ (cell12626 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12626 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12626 ⟨19,by decide⟩).lower ∧ (cell12626 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12626 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12626 ⟨20,by decide⟩).lower ∧ (cell12626 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12626 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12626 ⟨21,by decide⟩).lower ∧ (cell12626 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12626 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12626 ⟨22,by decide⟩).lower ∧ (cell12626 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12626 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12626 ⟨23,by decide⟩).lower ∧ (cell12626 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12626 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12626 ⟨24,by decide⟩).lower ∧ (cell12626 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12626 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12626 ⟨25,by decide⟩).lower ∧ (cell12626 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12626 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12626 ⟨26,by decide⟩).lower ∧ (cell12626 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12626 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12626 ⟨27,by decide⟩).lower ∧ (cell12626 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12626 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12626 ⟨28,by decide⟩).lower ∧ (cell12626 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12626 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12626 ⟨29,by decide⟩).lower ∧ (cell12626 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12626 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12626 ⟨30,by decide⟩).lower ∧ (cell12626 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12626 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12626 ⟨31,by decide⟩).lower ∧ (cell12626 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12626 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12626 ⟨32,by decide⟩).lower ∧ (cell12626 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12626 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12626 ⟨33,by decide⟩).lower ∧ (cell12626 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12626 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12626 ⟨34,by decide⟩).lower ∧ (cell12626 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12626 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12626 ⟨35,by decide⟩).lower ∧ (cell12626 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12626 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12626 ⟨36,by decide⟩).lower ∧ (cell12626 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12626 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12626 ⟨37,by decide⟩).lower ∧ (cell12626 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12626 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12626 ⟨38,by decide⟩).lower ∧ (cell12626 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12626 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12626 ⟨39,by decide⟩).lower ∧ (cell12626 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12626 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12626 ⟨40,by decide⟩).lower ∧ (cell12626 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12626 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12626 ⟨41,by decide⟩).lower ∧ (cell12626 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12626 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12626 ⟨42,by decide⟩).lower ∧ (cell12626 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12626 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12626 ⟨43,by decide⟩).lower ∧ (cell12626 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12626 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12626 ⟨44,by decide⟩).lower ∧ (cell12626 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12626 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12626 ⟨45,by decide⟩).lower ∧ (cell12626 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12626 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12626 ⟨46,by decide⟩).lower ∧ (cell12626 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12626 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12626 ⟨47,by decide⟩).lower ∧ (cell12626 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12626 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12626 ⟨48,by decide⟩).lower ∧ (cell12626 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12626 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12626 ⟨49,by decide⟩).lower ∧ (cell12626 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12626 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12626 ⟨50,by decide⟩).lower ∧ (cell12626 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12626 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12626 ⟨51,by decide⟩).lower ∧ (cell12626 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12626 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12626 ⟨52,by decide⟩).lower ∧ (cell12626 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12626 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12626 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12626 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12626,cell12626,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12626 i).lower ∧
    (cell12626 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12626 i).upper ≤ (0.532 : ℝ) ∧
    (cell12626 i).centre ≤ (0.1 : ℝ) ∧ (cell12626 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12626 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12626 i).centre = pilotGroupCentre (centreGroup i) := by
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
  | ⟨10,h⟩ => exact pilot_sourceCell10
  | ⟨11,h⟩ => exact pilot_sourceCell11
  | ⟨12,h⟩ => exact pilot_sourceCell12
  | ⟨13,h⟩ => exact pilot_sourceCell13
  | ⟨14,h⟩ => exact pilot_sourceCell14
  | ⟨15,h⟩ => exact pilot_sourceCell15
  | ⟨16,h⟩ => exact pilot_sourceCell16
  | ⟨17,h⟩ => exact pilot_sourceCell17
  | ⟨18,h⟩ => exact pilot_sourceCell18
  | ⟨19,h⟩ => exact pilot_sourceCell19
  | ⟨20,h⟩ => exact pilot_sourceCell20
  | ⟨21,h⟩ => exact pilot_sourceCell21
  | ⟨22,h⟩ => exact pilot_sourceCell22
  | ⟨23,h⟩ => exact pilot_sourceCell23
  | ⟨24,h⟩ => exact pilot_sourceCell24
  | ⟨25,h⟩ => exact pilot_sourceCell25
  | ⟨26,h⟩ => exact pilot_sourceCell26
  | ⟨27,h⟩ => exact pilot_sourceCell27
  | ⟨28,h⟩ => exact pilot_sourceCell28
  | ⟨29,h⟩ => exact pilot_sourceCell29
  | ⟨30,h⟩ => exact pilot_sourceCell30
  | ⟨31,h⟩ => exact pilot_sourceCell31
  | ⟨32,h⟩ => exact pilot_sourceCell32
  | ⟨33,h⟩ => exact pilot_sourceCell33
  | ⟨34,h⟩ => exact pilot_sourceCell34
  | ⟨35,h⟩ => exact pilot_sourceCell35
  | ⟨36,h⟩ => exact pilot_sourceCell36
  | ⟨37,h⟩ => exact pilot_sourceCell37
  | ⟨38,h⟩ => exact pilot_sourceCell38
  | ⟨39,h⟩ => exact pilot_sourceCell39
  | ⟨40,h⟩ => exact pilot_sourceCell40
  | ⟨41,h⟩ => exact pilot_sourceCell41
  | ⟨42,h⟩ => exact pilot_sourceCell42
  | ⟨43,h⟩ => exact pilot_sourceCell43
  | ⟨44,h⟩ => exact pilot_sourceCell44
  | ⟨45,h⟩ => exact pilot_sourceCell45
  | ⟨46,h⟩ => exact pilot_sourceCell46
  | ⟨47,h⟩ => exact pilot_sourceCell47
  | ⟨48,h⟩ => exact pilot_sourceCell48
  | ⟨49,h⟩ => exact pilot_sourceCell49
  | ⟨50,h⟩ => exact pilot_sourceCell50
  | ⟨51,h⟩ => exact pilot_sourceCell51
  | ⟨52,h⟩ => exact pilot_sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12626

/-! The local source numeric instances at 12626 have no network premises. -/
namespace BstLean.Part269.N12626
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12626)
open BstLean.Part268 (cell12626)

noncomputable def sourceNumerics12626 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12626 (cell12626 i)
      scalarRow12626.M scalarRow12626.H scalarRow12626.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := pilot_source_cell hi
  have E := pilot_upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := centreCertificate_from_moment (by norm_num)
      (G.window.2.trans (by norm_num)) (pilot_groupMomentCertificate hg)
      hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
    energy_allowance := scalarRow12626.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12626]
    centre_nonneg := (scalarRow12626.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12626])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12626
/-! Actual 12627 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12627
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12627 ≤ (1.035913494830 : ℝ) := by
  have hr : (112.369924801968 : ℝ) ≤ √(12627 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.369924801968 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12627 12627 (11 / 1000) ≤
    (0.008506609327 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12627) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.369924801968 : ℝ) ≤ √(12627 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12627)
  have hdiv : K / √(12627 : ℝ) ≤ K / 112.369924801968 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.369924801968 ≤ (0.008506609327 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12627.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12627 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12627 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12627 := gPlus_lower 12627
end BstLean.Part269.N12627

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12627
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035913494829 : ℝ) ≤ wn 12627 := by
  have hn : √(12627 : ℝ) ≤ 112.369924801969 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12627 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.369924801969 ≤ 2 / √(12627 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253362562 : ℝ) ≤ rhoBar 12627 BstLean.Part154.csC ∧
    rhoBar 12627 BstLean.Part154.csC ≤ 0.000253362954 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035913494829 : ℝ) / (1.295212 * 12627) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035913494830 : ℝ) / (1.29521 * 12627) := by gcongr
      _ ≤ (0.000253362954 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12627 BstLean.Part154.csC) ≤ 0.001013516009 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12627 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12627 BstLean.Part154.csC) (piBar (rhoBar 12627 BstLean.Part154.csC)) ≤ 0.000193520386 ∧
    cc1 (rhoBar 12627 BstLean.Part154.csC) (piBar (rhoBar 12627 BstLean.Part154.csC)) ≤ 0.000123138296 ∧
    cc2 (rhoBar 12627 BstLean.Part154.csC) ≤ 0.000071482711 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12627 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12627 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12627 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12627 BstLean.Part154.csC * nuR (rhoBar 12627 BstLean.Part154.csC)) ≤ 0.000506741956 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253362954 : ℝ) * 0.001013516009 := by gcongr
      _ ≤ (0.000506741956 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12627 BstLean.Part154.csC) * nuR (rhoBar 12627 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001013516009 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12627 BstLean.Part154.csC) * rhoBar 12627 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253362954 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253362954 / 2 + 0.399 * 0.001013516009 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193520386 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506741956 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123138296 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253362954 / 1.414213562 := by gcongr
      _ ≤ (0.000071482711 : ℝ) := by norm_num

end BstLean.Part269.N12627

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12627
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12627 BstLean.Part154.csC) (piBar (rhoBar 12627 BstLean.Part154.csC)) ≤ 1.61729E-7 := by
  have hr0 : 0 ≤ rhoBar 12627 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12627 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12627 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12627 BstLean.Part154.csC) (piBar (rhoBar 12627 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12627 BstLean.Part154.csC) (piBar (rhoBar 12627 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12627 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193520386 : ℝ) ^ 2 + 0.000123138296 ^ 2 + 3 * 0.000071482711 ^ 2 +
        2 * 0.797885 * 0.000193520386 * 0.000123138296 + 2 * 0.000193520386 * 0.000071482711 +
        4 * 0.797885 * 0.000123138296 * 0.000071482711 := by gcongr
    _ ≤ (1.61729E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12627 BstLean.Part154.csC Θ ≤ 0.002645019885 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12627 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12627 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12627 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12627 BstLean.Part154.csC) (piBar (rhoBar 12627 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12627 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035913494830 * 1.61729E-7 / (0.000253362562 : ℝ) := by gcongr
    _ ≤ 0.002645019885 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12627 BstLean.Part154.csC Θ ≤ 0.002935091238 + 0.000668354397 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12627 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12627 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12627 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035913494830 : ℝ) * ((2 * Θ * 0.000253362954 +
        (6863 / 10000) * 0.000253362954 * 12627 * 0.001013516009) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002935091238 + 0.000668354397 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12627 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12627 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12627 0.011 Θ ∧ gammaRatio 12627 0.011 Θ ≤ 0.000087099632 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12627 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035913494830 : ℝ) * 0.525 / ((1 - 0.011) * 12627) := by gcongr
      _ ≤ (0.000087099632 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12627 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12627 0.011 Θ) :=
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
    badAllowance 12627 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12627 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12627 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12627 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12627 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12627 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12627 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12627 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12627 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12627 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12627 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035913494830 : ℝ) * 12627 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12627 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003611797709 + 0.003313374282 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12627

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12627
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12627 BstLean.Part154.csC) (piBar (rhoBar 12627 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12627 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12627 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12627 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12627 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12627 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12627 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12627 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12627 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12627 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12627 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12627 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12627 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12627 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12627 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052637454408 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12627) ≤ 0.010627733205 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12627 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035913494830)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010627733205 + 2 * 0.737676 / 12627) := by gcongr
    _ ≤ (0.052637454408 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12627 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12627

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12627
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500247929 : ℝ) ≤ plow 12627 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12627) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052857919208)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388635440) : eMP 12627 0.011 xi bn ≤ 0.001195388116 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12627 : ℝ) * (1 - 0.011))) ≤ 0.000591045407 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001388635440 / (12627 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000591045407 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000591045407 : ℝ) + 3.141593 * 0.052857919208 / (12627 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001195388116 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052857919208)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388635440) : PiBarMP 12627 12 0.011 xi bn ≤ 0.161721255560 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12627 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037264399097 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.750181207906 : ℝ) ≤ √((12627 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.369924801968 : ℝ) ≤ √(12627 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12627) ≤ 0.123986985729 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037264399097 + 0.052857919208 * 1.772454 / (2 * (111.750181207906 : ℝ))) * (1 + 0.001195388116) +
        8 / (12627 * 112.369924801968) + 0.123986985729 := by gcongr
    _ ≤ (0.161721255560 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052857919208)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388635440) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282545956226) :
    parallelOracle 12627 0.011 xi bn cd ≤ 0.162717755928 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12627 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12627 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500247929 : ℝ) ≤ plow 12627 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.369924801968 : ℝ) ≤ √(12627 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282545956226 : ℝ) / (2 * 0.560500247929 * 112.369924801968)) * 0.161721255560 +
        0.282545956226 ^ 2 / (2 * 0.560500247929 * 112.369924801968) := by gcongr
    _ ≤ (0.162717755928 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052857919208) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388635440)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282545956226) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12627 12627 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500247929 : ℝ) ≤ plow 12627 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.369924801968 : ℝ) ≤ √(12627 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12627 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12627 Θ 1.22 ≤ 0.011801204837 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.369924801968 := by gcongr <;> linarith
      _ ≤ (0.011801204837 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12627 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12627 12627 0.011 ≤ 0.008506609327 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12627 12627 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12627 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12627 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12627 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12627 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162717755928 + 0.011801204837 + (0.008506609327 : ℝ) *
        (1 + 2 * (0.282545956226 + 0.011801204837) / (0.560500247929 * 112.369924801968))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12627]

end BstLean.Part269.N12627

/-! The original eight local profiles supply actual 12627 moment certificates. -/
namespace BstLean.Part269.N12627
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12627 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part253.group_scalar hg
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
      exact (mul_le_mul_of_nonneg_right (hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part253.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : NeededGroup g) :
    0 ≤ momentAllowance 12627 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12627 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052857919208 ∧
    0 ≤ bN 12627 BstLean.Part154.csC (groupTheta g) ∧ bN 12627 BstLean.Part154.csC (groupTheta g) ≤ 0.001388635440 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12627 12627 0.011
      (momentAllowance 12627 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12627 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12627 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12627 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12627 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12627 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229908501818 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12627 0.011
      (momentAllowance 12627 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12627 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12627
/-! The actual computed-centre upper energy formula at 12627. -/
namespace BstLean.Part269.N12627
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12627

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12627
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12627)
open BstLean.Part268 (cell12627)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085706106777
  | 2 => 0.086652889656
  | 3 => 0.087598411494
  | 4 => 0.088544227625
  | 5 => 0.089492214635
  | 6 => 0.090444617473
  | 7 => 0.091404100877
  | 8 => 0.092373805142
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12627 12627 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12627 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12627

/-! Actual upper energy certificates on all 43 source endpoints at 12627. -/
namespace BstLean.Part269.N12627
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12627)
open BstLean.Part268 (cell12627)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12627 (gMinus 12627) (1 - (cell12627 i).lower) ≤ 1 ∧
    energyUpper 12627 (gMinus 12627) (BstLean.Part211.gPlus 12627)
      (finiteEnergy 12627 12627 0.011) (1 - (cell12627 i).lower) ≤
      (cell12627 i).energy := by
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
  | ⟨10,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨10,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨11,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨12,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨13,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨14,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨15,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨16,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨17,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨18,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨19,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨20,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨21,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨22,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨23,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨24,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨25,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨26,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨27,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨28,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨29,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨30,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨31,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨32,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨33,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨34,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨35,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨36,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨37,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨38,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨39,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨40,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨41,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨42,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨43,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨44,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨45,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨46,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨47,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨48,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨49,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨50,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨51,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12627) (by norm_num)
        (q := 1 - (cell12627 ⟨52,by decide⟩).lower)
        (by norm_num [cell12627]) (by norm_num [cell12627])
      exact ⟨E.1,E.2.trans (by norm_num [cell12627])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12627

/-! Source-cell containment and simple scalar guards at 12627. -/
namespace BstLean.Part269.N12627
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12627)
open BstLean.Part268 (cell12627)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12627 ⟨10,by decide⟩).lower ∧ (cell12627 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12627 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12627 ⟨11,by decide⟩).lower ∧ (cell12627 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12627 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12627 ⟨12,by decide⟩).lower ∧ (cell12627 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12627 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12627 ⟨13,by decide⟩).lower ∧ (cell12627 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12627 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12627 ⟨14,by decide⟩).lower ∧ (cell12627 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12627 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12627 ⟨15,by decide⟩).lower ∧ (cell12627 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12627 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12627 ⟨16,by decide⟩).lower ∧ (cell12627 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12627 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12627 ⟨17,by decide⟩).lower ∧ (cell12627 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12627 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12627 ⟨18,by decide⟩).lower ∧ (cell12627 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12627 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12627 ⟨19,by decide⟩).lower ∧ (cell12627 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12627 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12627 ⟨20,by decide⟩).lower ∧ (cell12627 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12627 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12627 ⟨21,by decide⟩).lower ∧ (cell12627 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12627 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12627 ⟨22,by decide⟩).lower ∧ (cell12627 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12627 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12627 ⟨23,by decide⟩).lower ∧ (cell12627 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12627 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12627 ⟨24,by decide⟩).lower ∧ (cell12627 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12627 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12627 ⟨25,by decide⟩).lower ∧ (cell12627 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12627 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12627 ⟨26,by decide⟩).lower ∧ (cell12627 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12627 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12627 ⟨27,by decide⟩).lower ∧ (cell12627 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12627 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12627 ⟨28,by decide⟩).lower ∧ (cell12627 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12627 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12627 ⟨29,by decide⟩).lower ∧ (cell12627 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12627 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12627 ⟨30,by decide⟩).lower ∧ (cell12627 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12627 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12627 ⟨31,by decide⟩).lower ∧ (cell12627 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12627 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12627 ⟨32,by decide⟩).lower ∧ (cell12627 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12627 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12627 ⟨33,by decide⟩).lower ∧ (cell12627 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12627 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12627 ⟨34,by decide⟩).lower ∧ (cell12627 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12627 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12627 ⟨35,by decide⟩).lower ∧ (cell12627 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12627 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12627 ⟨36,by decide⟩).lower ∧ (cell12627 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12627 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12627 ⟨37,by decide⟩).lower ∧ (cell12627 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12627 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12627 ⟨38,by decide⟩).lower ∧ (cell12627 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12627 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12627 ⟨39,by decide⟩).lower ∧ (cell12627 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12627 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12627 ⟨40,by decide⟩).lower ∧ (cell12627 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12627 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12627 ⟨41,by decide⟩).lower ∧ (cell12627 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12627 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12627 ⟨42,by decide⟩).lower ∧ (cell12627 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12627 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12627 ⟨43,by decide⟩).lower ∧ (cell12627 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12627 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12627 ⟨44,by decide⟩).lower ∧ (cell12627 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12627 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12627 ⟨45,by decide⟩).lower ∧ (cell12627 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12627 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12627 ⟨46,by decide⟩).lower ∧ (cell12627 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12627 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12627 ⟨47,by decide⟩).lower ∧ (cell12627 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12627 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12627 ⟨48,by decide⟩).lower ∧ (cell12627 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12627 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12627 ⟨49,by decide⟩).lower ∧ (cell12627 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12627 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12627 ⟨50,by decide⟩).lower ∧ (cell12627 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12627 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12627 ⟨51,by decide⟩).lower ∧ (cell12627 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12627 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12627 ⟨52,by decide⟩).lower ∧ (cell12627 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12627 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12627 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12627 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12627,cell12627,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12627 i).lower ∧
    (cell12627 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12627 i).upper ≤ (0.532 : ℝ) ∧
    (cell12627 i).centre ≤ (0.1 : ℝ) ∧ (cell12627 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12627 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12627 i).centre = pilotGroupCentre (centreGroup i) := by
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
  | ⟨10,h⟩ => exact pilot_sourceCell10
  | ⟨11,h⟩ => exact pilot_sourceCell11
  | ⟨12,h⟩ => exact pilot_sourceCell12
  | ⟨13,h⟩ => exact pilot_sourceCell13
  | ⟨14,h⟩ => exact pilot_sourceCell14
  | ⟨15,h⟩ => exact pilot_sourceCell15
  | ⟨16,h⟩ => exact pilot_sourceCell16
  | ⟨17,h⟩ => exact pilot_sourceCell17
  | ⟨18,h⟩ => exact pilot_sourceCell18
  | ⟨19,h⟩ => exact pilot_sourceCell19
  | ⟨20,h⟩ => exact pilot_sourceCell20
  | ⟨21,h⟩ => exact pilot_sourceCell21
  | ⟨22,h⟩ => exact pilot_sourceCell22
  | ⟨23,h⟩ => exact pilot_sourceCell23
  | ⟨24,h⟩ => exact pilot_sourceCell24
  | ⟨25,h⟩ => exact pilot_sourceCell25
  | ⟨26,h⟩ => exact pilot_sourceCell26
  | ⟨27,h⟩ => exact pilot_sourceCell27
  | ⟨28,h⟩ => exact pilot_sourceCell28
  | ⟨29,h⟩ => exact pilot_sourceCell29
  | ⟨30,h⟩ => exact pilot_sourceCell30
  | ⟨31,h⟩ => exact pilot_sourceCell31
  | ⟨32,h⟩ => exact pilot_sourceCell32
  | ⟨33,h⟩ => exact pilot_sourceCell33
  | ⟨34,h⟩ => exact pilot_sourceCell34
  | ⟨35,h⟩ => exact pilot_sourceCell35
  | ⟨36,h⟩ => exact pilot_sourceCell36
  | ⟨37,h⟩ => exact pilot_sourceCell37
  | ⟨38,h⟩ => exact pilot_sourceCell38
  | ⟨39,h⟩ => exact pilot_sourceCell39
  | ⟨40,h⟩ => exact pilot_sourceCell40
  | ⟨41,h⟩ => exact pilot_sourceCell41
  | ⟨42,h⟩ => exact pilot_sourceCell42
  | ⟨43,h⟩ => exact pilot_sourceCell43
  | ⟨44,h⟩ => exact pilot_sourceCell44
  | ⟨45,h⟩ => exact pilot_sourceCell45
  | ⟨46,h⟩ => exact pilot_sourceCell46
  | ⟨47,h⟩ => exact pilot_sourceCell47
  | ⟨48,h⟩ => exact pilot_sourceCell48
  | ⟨49,h⟩ => exact pilot_sourceCell49
  | ⟨50,h⟩ => exact pilot_sourceCell50
  | ⟨51,h⟩ => exact pilot_sourceCell51
  | ⟨52,h⟩ => exact pilot_sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12627

/-! The local source numeric instances at 12627 have no network premises. -/
namespace BstLean.Part269.N12627
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12627)
open BstLean.Part268 (cell12627)

noncomputable def sourceNumerics12627 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12627 (cell12627 i)
      scalarRow12627.M scalarRow12627.H scalarRow12627.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := pilot_source_cell hi
  have E := pilot_upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := centreCertificate_from_moment (by norm_num)
      (G.window.2.trans (by norm_num)) (pilot_groupMomentCertificate hg)
      hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
    energy_allowance := scalarRow12627.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12627]
    centre_nonneg := (scalarRow12627.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12627])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12627
/-! Actual 12628 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12628
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12628 ≤ (1.035912060280 : ℝ) := by
  have hr : (112.374374303041 : ℝ) ≤ √(12628 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.374374303041 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12628 12628 (11 / 1000) ≤
    (0.008506272502 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12628) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.374374303041 : ℝ) ≤ √(12628 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12628)
  have hdiv : K / √(12628 : ℝ) ≤ K / 112.374374303041 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.374374303041 ≤ (0.008506272502 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12628.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12628 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12628 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12628 := gPlus_lower 12628
end BstLean.Part269.N12628

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12628
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035912060279 : ℝ) ≤ wn 12628 := by
  have hn : √(12628 : ℝ) ≤ 112.374374303042 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12628 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.374374303042 ≤ 2 / √(12628 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253342147 : ℝ) ≤ rhoBar 12628 BstLean.Part154.csC ∧
    rhoBar 12628 BstLean.Part154.csC ≤ 0.000253342539 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035912060279 : ℝ) / (1.295212 * 12628) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035912060280 : ℝ) / (1.29521 * 12628) := by gcongr
      _ ≤ (0.000253342539 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12628 BstLean.Part154.csC) ≤ 0.001013434339 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12628 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12628 BstLean.Part154.csC) (piBar (rhoBar 12628 BstLean.Part154.csC)) ≤ 0.000193504793 ∧
    cc1 (rhoBar 12628 BstLean.Part154.csC) (piBar (rhoBar 12628 BstLean.Part154.csC)) ≤ 0.000123128374 ∧
    cc2 (rhoBar 12628 BstLean.Part154.csC) ≤ 0.000071476951 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12628 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12628 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12628 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12628 BstLean.Part154.csC * nuR (rhoBar 12628 BstLean.Part154.csC)) ≤ 0.000506701124 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253342539 : ℝ) * 0.001013434339 := by gcongr
      _ ≤ (0.000506701124 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12628 BstLean.Part154.csC) * nuR (rhoBar 12628 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001013434339 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12628 BstLean.Part154.csC) * rhoBar 12628 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253342539 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253342539 / 2 + 0.399 * 0.001013434339 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193504793 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506701124 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123128374 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253342539 / 1.414213562 := by gcongr
      _ ≤ (0.000071476951 : ℝ) := by norm_num

end BstLean.Part269.N12628

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12628
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12628 BstLean.Part154.csC) (piBar (rhoBar 12628 BstLean.Part154.csC)) ≤ 1.61703E-7 := by
  have hr0 : 0 ≤ rhoBar 12628 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12628 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12628 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12628 BstLean.Part154.csC) (piBar (rhoBar 12628 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12628 BstLean.Part154.csC) (piBar (rhoBar 12628 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12628 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193504793 : ℝ) ^ 2 + 0.000123128374 ^ 2 + 3 * 0.000071476951 ^ 2 +
        2 * 0.797885 * 0.000193504793 * 0.000123128374 + 2 * 0.000193504793 * 0.000071476951 +
        4 * 0.797885 * 0.000123128374 * 0.000071476951 := by gcongr
    _ ≤ (1.61703E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12628 BstLean.Part154.csC Θ ≤ 0.002644804110 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12628 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12628 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12628 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12628 BstLean.Part154.csC) (piBar (rhoBar 12628 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12628 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035912060280 * 1.61703E-7 / (0.000253342147 : ℝ) := by gcongr
    _ ≤ 0.002644804110 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12628 BstLean.Part154.csC Θ ≤ 0.002934846591 + 0.000668299618 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12628 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12628 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12628 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035912060280 : ℝ) * ((2 * Θ * 0.000253342539 +
        (6863 / 10000) * 0.000253342539 * 12628 * 0.001013434339) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002934846591 + 0.000668299618 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12628 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12628 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12628 0.011 Θ ∧ gammaRatio 12628 0.011 Θ ≤ 0.000087092614 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12628 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035912060280 : ℝ) * 0.525 / ((1 - 0.011) * 12628) := by gcongr
      _ ≤ (0.000087092614 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12628 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12628 0.011 Θ) :=
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
    badAllowance 12628 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12628 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12628 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12628 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12628 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12628 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12628 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12628 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12628 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12628 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12628 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035912060280 : ℝ) * 12628 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12628 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003611553062 + 0.003313103728 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12628

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12628
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12628 BstLean.Part154.csC) (piBar (rhoBar 12628 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12628 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12628 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12628 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12628 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12628 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12628 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12628 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12628 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12628 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12628 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12628 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12628 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12628 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12628 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052635347550 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12628) ≤ 0.010627312397 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12628 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035912060280)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010627312397 + 2 * 0.737676 / 12628) := by gcongr
    _ ≤ (0.052635347550 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12628 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12628

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12628
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500293672 : ℝ) ≤ plow 12628 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12628) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052857532520)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388522158) : eMP 12628 0.011 xi bn ≤ 0.001195291946 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12628 : ℝ) * (1 - 0.011))) ≤ 0.000590997897 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001388522158 / (12628 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590997897 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590997897 : ℝ) + 3.141593 * 0.052857532520 / (12628 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001195291946 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052857532520)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388522158) : PiBarMP 12628 12 0.011 xi bn ≤ 0.161714800447 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12628 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037262879089 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.754606169052 : ℝ) ≤ √((12628 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.374374303041 : ℝ) ≤ √(12628 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12628) ≤ 0.123982076423 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037262879089 + 0.052857532520 * 1.772454 / (2 * (111.754606169052 : ℝ))) * (1 + 0.001195291946) +
        8 / (12628 * 112.374374303041) + 0.123982076423 := by gcongr
    _ ≤ (0.161714800447 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052857532520)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388522158) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282543008406) :
    parallelOracle 12628 0.011 xi bn cd ≤ 0.162711229791 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12628 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12628 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500293672 : ℝ) ≤ plow 12628 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.374374303041 : ℝ) ≤ √(12628 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282543008406 : ℝ) / (2 * 0.560500293672 * 112.374374303041)) * 0.161714800447 +
        0.282543008406 ^ 2 / (2 * 0.560500293672 * 112.374374303041) := by gcongr
    _ ≤ (0.162711229791 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052857532520) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388522158)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282543008406) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12628 12628 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500293672 : ℝ) ≤ plow 12628 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.374374303041 : ℝ) ≤ √(12628 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12628 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12628 Θ 1.22 ≤ 0.011800737564 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.374374303041 := by gcongr <;> linarith
      _ ≤ (0.011800737564 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12628 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12628 12628 0.011 ≤ 0.008506272502 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12628 12628 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12628 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12628 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12628 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12628 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162711229791 + 0.011800737564 + (0.008506272502 : ℝ) *
        (1 + 2 * (0.282543008406 + 0.011800737564) / (0.560500293672 * 112.374374303041))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12628]

end BstLean.Part269.N12628

/-! The original eight local profiles supply actual 12628 moment certificates. -/
namespace BstLean.Part269.N12628
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12628 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part253.group_scalar hg
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
      exact (mul_le_mul_of_nonneg_right (hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part253.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : NeededGroup g) :
    0 ≤ momentAllowance 12628 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12628 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052857532520 ∧
    0 ≤ bN 12628 BstLean.Part154.csC (groupTheta g) ∧ bN 12628 BstLean.Part154.csC (groupTheta g) ≤ 0.001388522158 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12628 12628 0.011
      (momentAllowance 12628 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12628 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12628 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12628 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12628 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12628 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229907660856 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12628 0.011
      (momentAllowance 12628 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12628 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12628
/-! The actual computed-centre upper energy formula at 12628. -/
namespace BstLean.Part269.N12628
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12628

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12628
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12628)
open BstLean.Part268 (cell12628)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085703108919
  | 2 => 0.086649834837
  | 3 => 0.087595291104
  | 4 => 0.088541031091
  | 5 => 0.089488929082
  | 6 => 0.090441227337
  | 7 => 0.091400587480
  | 8 => 0.092370146212
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12628 12628 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12628 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12628

/-! Actual upper energy certificates on all 43 source endpoints at 12628. -/
namespace BstLean.Part269.N12628
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12628)
open BstLean.Part268 (cell12628)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12628 (gMinus 12628) (1 - (cell12628 i).lower) ≤ 1 ∧
    energyUpper 12628 (gMinus 12628) (BstLean.Part211.gPlus 12628)
      (finiteEnergy 12628 12628 0.011) (1 - (cell12628 i).lower) ≤
      (cell12628 i).energy := by
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
  | ⟨10,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨10,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨11,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨12,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨13,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨14,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨15,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨16,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨17,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨18,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨19,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨20,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨21,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨22,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨23,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨24,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨25,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨26,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨27,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨28,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨29,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨30,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨31,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨32,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨33,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨34,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨35,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨36,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨37,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨38,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨39,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨40,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨41,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨42,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨43,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨44,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨45,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨46,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨47,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨48,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨49,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨50,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨51,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12628) (by norm_num)
        (q := 1 - (cell12628 ⟨52,by decide⟩).lower)
        (by norm_num [cell12628]) (by norm_num [cell12628])
      exact ⟨E.1,E.2.trans (by norm_num [cell12628])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12628

/-! Source-cell containment and simple scalar guards at 12628. -/
namespace BstLean.Part269.N12628
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12628)
open BstLean.Part268 (cell12628)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12628 ⟨10,by decide⟩).lower ∧ (cell12628 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12628 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12628 ⟨11,by decide⟩).lower ∧ (cell12628 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12628 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12628 ⟨12,by decide⟩).lower ∧ (cell12628 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12628 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12628 ⟨13,by decide⟩).lower ∧ (cell12628 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12628 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12628 ⟨14,by decide⟩).lower ∧ (cell12628 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12628 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12628 ⟨15,by decide⟩).lower ∧ (cell12628 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12628 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12628 ⟨16,by decide⟩).lower ∧ (cell12628 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12628 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12628 ⟨17,by decide⟩).lower ∧ (cell12628 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12628 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12628 ⟨18,by decide⟩).lower ∧ (cell12628 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12628 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12628 ⟨19,by decide⟩).lower ∧ (cell12628 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12628 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12628 ⟨20,by decide⟩).lower ∧ (cell12628 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12628 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12628 ⟨21,by decide⟩).lower ∧ (cell12628 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12628 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12628 ⟨22,by decide⟩).lower ∧ (cell12628 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12628 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12628 ⟨23,by decide⟩).lower ∧ (cell12628 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12628 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12628 ⟨24,by decide⟩).lower ∧ (cell12628 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12628 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12628 ⟨25,by decide⟩).lower ∧ (cell12628 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12628 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12628 ⟨26,by decide⟩).lower ∧ (cell12628 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12628 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12628 ⟨27,by decide⟩).lower ∧ (cell12628 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12628 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12628 ⟨28,by decide⟩).lower ∧ (cell12628 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12628 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12628 ⟨29,by decide⟩).lower ∧ (cell12628 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12628 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12628 ⟨30,by decide⟩).lower ∧ (cell12628 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12628 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12628 ⟨31,by decide⟩).lower ∧ (cell12628 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12628 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12628 ⟨32,by decide⟩).lower ∧ (cell12628 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12628 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12628 ⟨33,by decide⟩).lower ∧ (cell12628 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12628 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12628 ⟨34,by decide⟩).lower ∧ (cell12628 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12628 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12628 ⟨35,by decide⟩).lower ∧ (cell12628 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12628 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12628 ⟨36,by decide⟩).lower ∧ (cell12628 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12628 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12628 ⟨37,by decide⟩).lower ∧ (cell12628 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12628 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12628 ⟨38,by decide⟩).lower ∧ (cell12628 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12628 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12628 ⟨39,by decide⟩).lower ∧ (cell12628 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12628 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12628 ⟨40,by decide⟩).lower ∧ (cell12628 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12628 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12628 ⟨41,by decide⟩).lower ∧ (cell12628 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12628 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12628 ⟨42,by decide⟩).lower ∧ (cell12628 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12628 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12628 ⟨43,by decide⟩).lower ∧ (cell12628 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12628 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12628 ⟨44,by decide⟩).lower ∧ (cell12628 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12628 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12628 ⟨45,by decide⟩).lower ∧ (cell12628 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12628 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12628 ⟨46,by decide⟩).lower ∧ (cell12628 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12628 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12628 ⟨47,by decide⟩).lower ∧ (cell12628 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12628 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12628 ⟨48,by decide⟩).lower ∧ (cell12628 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12628 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12628 ⟨49,by decide⟩).lower ∧ (cell12628 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12628 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12628 ⟨50,by decide⟩).lower ∧ (cell12628 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12628 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12628 ⟨51,by decide⟩).lower ∧ (cell12628 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12628 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12628 ⟨52,by decide⟩).lower ∧ (cell12628 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12628 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12628 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12628 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12628,cell12628,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12628 i).lower ∧
    (cell12628 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12628 i).upper ≤ (0.532 : ℝ) ∧
    (cell12628 i).centre ≤ (0.1 : ℝ) ∧ (cell12628 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12628 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12628 i).centre = pilotGroupCentre (centreGroup i) := by
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
  | ⟨10,h⟩ => exact pilot_sourceCell10
  | ⟨11,h⟩ => exact pilot_sourceCell11
  | ⟨12,h⟩ => exact pilot_sourceCell12
  | ⟨13,h⟩ => exact pilot_sourceCell13
  | ⟨14,h⟩ => exact pilot_sourceCell14
  | ⟨15,h⟩ => exact pilot_sourceCell15
  | ⟨16,h⟩ => exact pilot_sourceCell16
  | ⟨17,h⟩ => exact pilot_sourceCell17
  | ⟨18,h⟩ => exact pilot_sourceCell18
  | ⟨19,h⟩ => exact pilot_sourceCell19
  | ⟨20,h⟩ => exact pilot_sourceCell20
  | ⟨21,h⟩ => exact pilot_sourceCell21
  | ⟨22,h⟩ => exact pilot_sourceCell22
  | ⟨23,h⟩ => exact pilot_sourceCell23
  | ⟨24,h⟩ => exact pilot_sourceCell24
  | ⟨25,h⟩ => exact pilot_sourceCell25
  | ⟨26,h⟩ => exact pilot_sourceCell26
  | ⟨27,h⟩ => exact pilot_sourceCell27
  | ⟨28,h⟩ => exact pilot_sourceCell28
  | ⟨29,h⟩ => exact pilot_sourceCell29
  | ⟨30,h⟩ => exact pilot_sourceCell30
  | ⟨31,h⟩ => exact pilot_sourceCell31
  | ⟨32,h⟩ => exact pilot_sourceCell32
  | ⟨33,h⟩ => exact pilot_sourceCell33
  | ⟨34,h⟩ => exact pilot_sourceCell34
  | ⟨35,h⟩ => exact pilot_sourceCell35
  | ⟨36,h⟩ => exact pilot_sourceCell36
  | ⟨37,h⟩ => exact pilot_sourceCell37
  | ⟨38,h⟩ => exact pilot_sourceCell38
  | ⟨39,h⟩ => exact pilot_sourceCell39
  | ⟨40,h⟩ => exact pilot_sourceCell40
  | ⟨41,h⟩ => exact pilot_sourceCell41
  | ⟨42,h⟩ => exact pilot_sourceCell42
  | ⟨43,h⟩ => exact pilot_sourceCell43
  | ⟨44,h⟩ => exact pilot_sourceCell44
  | ⟨45,h⟩ => exact pilot_sourceCell45
  | ⟨46,h⟩ => exact pilot_sourceCell46
  | ⟨47,h⟩ => exact pilot_sourceCell47
  | ⟨48,h⟩ => exact pilot_sourceCell48
  | ⟨49,h⟩ => exact pilot_sourceCell49
  | ⟨50,h⟩ => exact pilot_sourceCell50
  | ⟨51,h⟩ => exact pilot_sourceCell51
  | ⟨52,h⟩ => exact pilot_sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12628

/-! The local source numeric instances at 12628 have no network premises. -/
namespace BstLean.Part269.N12628
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12628)
open BstLean.Part268 (cell12628)

noncomputable def sourceNumerics12628 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12628 (cell12628 i)
      scalarRow12628.M scalarRow12628.H scalarRow12628.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := pilot_source_cell hi
  have E := pilot_upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := centreCertificate_from_moment (by norm_num)
      (G.window.2.trans (by norm_num)) (pilot_groupMomentCertificate hg)
      hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
    energy_allowance := scalarRow12628.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12628]
    centre_nonneg := (scalarRow12628.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12628])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12628
/-! Actual 12629 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12629
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12629 ≤ (1.035910625902 : ℝ) := by
  have hr : (112.378823627941 : ℝ) ≤ √(12629 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.378823627941 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12629 12629 (11 / 1000) ≤
    (0.008505935717 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12629) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.378823627941 : ℝ) ≤ √(12629 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12629)
  have hdiv : K / √(12629 : ℝ) ≤ K / 112.378823627941 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.378823627941 ≤ (0.008505935717 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12629.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12629 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12629 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12629 := gPlus_lower 12629
end BstLean.Part269.N12629

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12629
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035910625901 : ℝ) ≤ wn 12629 := by
  have hn : √(12629 : ℝ) ≤ 112.378823627942 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12629 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.378823627942 ≤ 2 / √(12629 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253321736 : ℝ) ≤ rhoBar 12629 BstLean.Part154.csC ∧
    rhoBar 12629 BstLean.Part154.csC ≤ 0.000253322128 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035910625901 : ℝ) / (1.295212 * 12629) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035910625902 : ℝ) / (1.29521 * 12629) := by gcongr
      _ ≤ (0.000253322128 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12629 BstLean.Part154.csC) ≤ 0.001013352685 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12629 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12629 BstLean.Part154.csC) (piBar (rhoBar 12629 BstLean.Part154.csC)) ≤ 0.000193489202 ∧
    cc1 (rhoBar 12629 BstLean.Part154.csC) (piBar (rhoBar 12629 BstLean.Part154.csC)) ≤ 0.000123118453 ∧
    cc2 (rhoBar 12629 BstLean.Part154.csC) ≤ 0.000071471193 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12629 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12629 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12629 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12629 BstLean.Part154.csC * nuR (rhoBar 12629 BstLean.Part154.csC)) ≤ 0.000506660299 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253322128 : ℝ) * 0.001013352685 := by gcongr
      _ ≤ (0.000506660299 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12629 BstLean.Part154.csC) * nuR (rhoBar 12629 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001013352685 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12629 BstLean.Part154.csC) * rhoBar 12629 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253322128 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253322128 / 2 + 0.399 * 0.001013352685 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193489202 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506660299 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123118453 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253322128 / 1.414213562 := by gcongr
      _ ≤ (0.000071471193 : ℝ) := by norm_num

end BstLean.Part269.N12629

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12629
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12629 BstLean.Part154.csC) (piBar (rhoBar 12629 BstLean.Part154.csC)) ≤ 1.61677E-7 := by
  have hr0 : 0 ≤ rhoBar 12629 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12629 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12629 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12629 BstLean.Part154.csC) (piBar (rhoBar 12629 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12629 BstLean.Part154.csC) (piBar (rhoBar 12629 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12629 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193489202 : ℝ) ^ 2 + 0.000123118453 ^ 2 + 3 * 0.000071471193 ^ 2 +
        2 * 0.797885 * 0.000193489202 * 0.000123118453 + 2 * 0.000193489202 * 0.000071471193 +
        4 * 0.797885 * 0.000123118453 * 0.000071471193 := by gcongr
    _ ≤ (1.61677E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12629 BstLean.Part154.csC Θ ≤ 0.002644588261 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12629 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12629 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12629 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12629 BstLean.Part154.csC) (piBar (rhoBar 12629 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12629 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035910625902 * 1.61677E-7 / (0.000253321736 : ℝ) := by gcongr
    _ ≤ 0.002644588261 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12629 BstLean.Part154.csC Θ ≤ 0.002934602000 + 0.000668244850 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12629 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12629 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12629 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035910625902 : ℝ) * ((2 * Θ * 0.000253322128 +
        (6863 / 10000) * 0.000253322128 * 12629 * 0.001013352685) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002934602000 + 0.000668244850 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12629 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12629 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12629 0.011 Θ ∧ gammaRatio 12629 0.011 Θ ≤ 0.000087085597 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12629 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035910625902 : ℝ) * 0.525 / ((1 - 0.011) * 12629) := by gcongr
      _ ≤ (0.000087085597 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12629 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12629 0.011 Θ) :=
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
    badAllowance 12629 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12629 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12629 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12629 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12629 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12629 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12629 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12629 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12629 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12629 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12629 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035910625902 : ℝ) * 12629 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12629 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003611308471 + 0.003312833111 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12629

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12629
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12629 BstLean.Part154.csC) (piBar (rhoBar 12629 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12629 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12629 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12629 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12629 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12629 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12629 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12629 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12629 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12629 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12629 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12629 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12629 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12629 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12629 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052633240939 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12629) ≤ 0.010626891638 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12629 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035910625902)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010626891638 + 2 * 0.737676 / 12629) := by gcongr
    _ ≤ (0.052633240939 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12629 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12629

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12629
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500339409 : ℝ) ≤ plow 12629 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12629) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052857145855)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388408838) : eMP 12629 0.011 xi bn ≤ 0.001195195766 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12629 : ℝ) * (1 - 0.011))) ≤ 0.000590950382 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001388408838 / (12629 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590950382 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590950382 : ℝ) + 3.141593 * 0.052857145855 / (12629 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001195195766 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052857145855)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388408838) : PiBarMP 12629 12 0.011 xi bn ≤ 0.161708345349 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12629 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037261358510 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.759030954997 : ℝ) ≤ √((12629 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.378823627941 : ℝ) ≤ √(12629 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12629) ≤ 0.123977167700 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037261358510 + 0.052857145855 * 1.772454 / (2 * (111.759030954997 : ℝ))) * (1 + 0.001195195766) +
        8 / (12629 * 112.378823627941) + 0.123977167700 := by gcongr
    _ ≤ (0.161708345349 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052857145855)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388408838) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282540060880) :
    parallelOracle 12629 0.011 xi bn cd ≤ 0.162704703679 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12629 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12629 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500339409 : ℝ) ≤ plow 12629 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.378823627941 : ℝ) ≤ √(12629 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282540060880 : ℝ) / (2 * 0.560500339409 * 112.378823627941)) * 0.161708345349 +
        0.282540060880 ^ 2 / (2 * 0.560500339409 * 112.378823627941) := by gcongr
    _ ≤ (0.162704703679 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052857145855) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388408838)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282540060880) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12629 12629 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500339409 : ℝ) ≤ plow 12629 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.378823627941 : ℝ) ≤ √(12629 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12629 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12629 Θ 1.22 ≤ 0.011800270347 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.378823627941 := by gcongr <;> linarith
      _ ≤ (0.011800270347 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12629 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12629 12629 0.011 ≤ 0.008505935717 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12629 12629 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12629 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12629 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12629 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12629 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162704703679 + 0.011800270347 + (0.008505935717 : ℝ) *
        (1 + 2 * (0.282540060880 + 0.011800270347) / (0.560500339409 * 112.378823627941))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12629]

end BstLean.Part269.N12629

/-! The original eight local profiles supply actual 12629 moment certificates. -/
namespace BstLean.Part269.N12629
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12629 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part253.group_scalar hg
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
      exact (mul_le_mul_of_nonneg_right (hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part253.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : NeededGroup g) :
    0 ≤ momentAllowance 12629 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12629 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052857145855 ∧
    0 ≤ bN 12629 BstLean.Part154.csC (groupTheta g) ∧ bN 12629 BstLean.Part154.csC (groupTheta g) ≤ 0.001388408838 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12629 12629 0.011
      (momentAllowance 12629 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12629 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12629 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12629 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12629 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12629 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229906819941 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12629 0.011
      (momentAllowance 12629 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12629 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12629
/-! The actual computed-centre upper energy formula at 12629. -/
namespace BstLean.Part269.N12629
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12629

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12629
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12629)
open BstLean.Part268 (cell12629)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085700112227
  | 2 => 0.086646781233
  | 3 => 0.087592171989
  | 4 => 0.088537835908
  | 5 => 0.089485644970
  | 6 => 0.090437838753
  | 7 => 0.091397075766
  | 8 => 0.092366489126
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12629 12629 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12629 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12629

/-! Actual upper energy certificates on all 43 source endpoints at 12629. -/
namespace BstLean.Part269.N12629
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12629)
open BstLean.Part268 (cell12629)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12629 (gMinus 12629) (1 - (cell12629 i).lower) ≤ 1 ∧
    energyUpper 12629 (gMinus 12629) (BstLean.Part211.gPlus 12629)
      (finiteEnergy 12629 12629 0.011) (1 - (cell12629 i).lower) ≤
      (cell12629 i).energy := by
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
  | ⟨10,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨10,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨11,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨12,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨13,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨14,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨15,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨16,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨17,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨18,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨19,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨20,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨21,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨22,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨23,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨24,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨25,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨26,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨27,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨28,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨29,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨30,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨31,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨32,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨33,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨34,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨35,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨36,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨37,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨38,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨39,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨40,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨41,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨42,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨43,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨44,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨45,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨46,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨47,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨48,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨49,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨50,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨51,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12629) (by norm_num)
        (q := 1 - (cell12629 ⟨52,by decide⟩).lower)
        (by norm_num [cell12629]) (by norm_num [cell12629])
      exact ⟨E.1,E.2.trans (by norm_num [cell12629])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12629

/-! Source-cell containment and simple scalar guards at 12629. -/
namespace BstLean.Part269.N12629
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12629)
open BstLean.Part268 (cell12629)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12629 ⟨10,by decide⟩).lower ∧ (cell12629 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12629 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12629 ⟨11,by decide⟩).lower ∧ (cell12629 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12629 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12629 ⟨12,by decide⟩).lower ∧ (cell12629 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12629 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12629 ⟨13,by decide⟩).lower ∧ (cell12629 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12629 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12629 ⟨14,by decide⟩).lower ∧ (cell12629 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12629 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12629 ⟨15,by decide⟩).lower ∧ (cell12629 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12629 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12629 ⟨16,by decide⟩).lower ∧ (cell12629 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12629 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12629 ⟨17,by decide⟩).lower ∧ (cell12629 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12629 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12629 ⟨18,by decide⟩).lower ∧ (cell12629 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12629 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12629 ⟨19,by decide⟩).lower ∧ (cell12629 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12629 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12629 ⟨20,by decide⟩).lower ∧ (cell12629 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12629 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12629 ⟨21,by decide⟩).lower ∧ (cell12629 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12629 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12629 ⟨22,by decide⟩).lower ∧ (cell12629 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12629 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12629 ⟨23,by decide⟩).lower ∧ (cell12629 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12629 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12629 ⟨24,by decide⟩).lower ∧ (cell12629 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12629 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12629 ⟨25,by decide⟩).lower ∧ (cell12629 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12629 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12629 ⟨26,by decide⟩).lower ∧ (cell12629 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12629 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12629 ⟨27,by decide⟩).lower ∧ (cell12629 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12629 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12629 ⟨28,by decide⟩).lower ∧ (cell12629 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12629 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12629 ⟨29,by decide⟩).lower ∧ (cell12629 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12629 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12629 ⟨30,by decide⟩).lower ∧ (cell12629 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12629 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12629 ⟨31,by decide⟩).lower ∧ (cell12629 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12629 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12629 ⟨32,by decide⟩).lower ∧ (cell12629 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12629 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12629 ⟨33,by decide⟩).lower ∧ (cell12629 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12629 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12629 ⟨34,by decide⟩).lower ∧ (cell12629 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12629 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12629 ⟨35,by decide⟩).lower ∧ (cell12629 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12629 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12629 ⟨36,by decide⟩).lower ∧ (cell12629 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12629 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12629 ⟨37,by decide⟩).lower ∧ (cell12629 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12629 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12629 ⟨38,by decide⟩).lower ∧ (cell12629 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12629 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12629 ⟨39,by decide⟩).lower ∧ (cell12629 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12629 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12629 ⟨40,by decide⟩).lower ∧ (cell12629 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12629 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12629 ⟨41,by decide⟩).lower ∧ (cell12629 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12629 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12629 ⟨42,by decide⟩).lower ∧ (cell12629 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12629 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12629 ⟨43,by decide⟩).lower ∧ (cell12629 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12629 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12629 ⟨44,by decide⟩).lower ∧ (cell12629 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12629 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12629 ⟨45,by decide⟩).lower ∧ (cell12629 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12629 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12629 ⟨46,by decide⟩).lower ∧ (cell12629 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12629 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12629 ⟨47,by decide⟩).lower ∧ (cell12629 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12629 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12629 ⟨48,by decide⟩).lower ∧ (cell12629 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12629 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12629 ⟨49,by decide⟩).lower ∧ (cell12629 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12629 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12629 ⟨50,by decide⟩).lower ∧ (cell12629 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12629 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12629 ⟨51,by decide⟩).lower ∧ (cell12629 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12629 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12629 ⟨52,by decide⟩).lower ∧ (cell12629 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12629 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12629 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12629 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12629,cell12629,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12629 i).lower ∧
    (cell12629 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12629 i).upper ≤ (0.532 : ℝ) ∧
    (cell12629 i).centre ≤ (0.1 : ℝ) ∧ (cell12629 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12629 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12629 i).centre = pilotGroupCentre (centreGroup i) := by
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
  | ⟨10,h⟩ => exact pilot_sourceCell10
  | ⟨11,h⟩ => exact pilot_sourceCell11
  | ⟨12,h⟩ => exact pilot_sourceCell12
  | ⟨13,h⟩ => exact pilot_sourceCell13
  | ⟨14,h⟩ => exact pilot_sourceCell14
  | ⟨15,h⟩ => exact pilot_sourceCell15
  | ⟨16,h⟩ => exact pilot_sourceCell16
  | ⟨17,h⟩ => exact pilot_sourceCell17
  | ⟨18,h⟩ => exact pilot_sourceCell18
  | ⟨19,h⟩ => exact pilot_sourceCell19
  | ⟨20,h⟩ => exact pilot_sourceCell20
  | ⟨21,h⟩ => exact pilot_sourceCell21
  | ⟨22,h⟩ => exact pilot_sourceCell22
  | ⟨23,h⟩ => exact pilot_sourceCell23
  | ⟨24,h⟩ => exact pilot_sourceCell24
  | ⟨25,h⟩ => exact pilot_sourceCell25
  | ⟨26,h⟩ => exact pilot_sourceCell26
  | ⟨27,h⟩ => exact pilot_sourceCell27
  | ⟨28,h⟩ => exact pilot_sourceCell28
  | ⟨29,h⟩ => exact pilot_sourceCell29
  | ⟨30,h⟩ => exact pilot_sourceCell30
  | ⟨31,h⟩ => exact pilot_sourceCell31
  | ⟨32,h⟩ => exact pilot_sourceCell32
  | ⟨33,h⟩ => exact pilot_sourceCell33
  | ⟨34,h⟩ => exact pilot_sourceCell34
  | ⟨35,h⟩ => exact pilot_sourceCell35
  | ⟨36,h⟩ => exact pilot_sourceCell36
  | ⟨37,h⟩ => exact pilot_sourceCell37
  | ⟨38,h⟩ => exact pilot_sourceCell38
  | ⟨39,h⟩ => exact pilot_sourceCell39
  | ⟨40,h⟩ => exact pilot_sourceCell40
  | ⟨41,h⟩ => exact pilot_sourceCell41
  | ⟨42,h⟩ => exact pilot_sourceCell42
  | ⟨43,h⟩ => exact pilot_sourceCell43
  | ⟨44,h⟩ => exact pilot_sourceCell44
  | ⟨45,h⟩ => exact pilot_sourceCell45
  | ⟨46,h⟩ => exact pilot_sourceCell46
  | ⟨47,h⟩ => exact pilot_sourceCell47
  | ⟨48,h⟩ => exact pilot_sourceCell48
  | ⟨49,h⟩ => exact pilot_sourceCell49
  | ⟨50,h⟩ => exact pilot_sourceCell50
  | ⟨51,h⟩ => exact pilot_sourceCell51
  | ⟨52,h⟩ => exact pilot_sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12629

/-! The local source numeric instances at 12629 have no network premises. -/
namespace BstLean.Part269.N12629
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12629)
open BstLean.Part268 (cell12629)

noncomputable def sourceNumerics12629 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12629 (cell12629 i)
      scalarRow12629.M scalarRow12629.H scalarRow12629.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := pilot_source_cell hi
  have E := pilot_upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := centreCertificate_from_moment (by norm_num)
      (G.window.2.trans (by norm_num)) (pilot_groupMomentCertificate hg)
      hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
    energy_allowance := scalarRow12629.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12629]
    centre_nonneg := (scalarRow12629.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12629])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12629
/-! Actual 12630 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12630
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12630 ≤ (1.035909191695 : ℝ) := by
  have hr : (112.383272776690 : ℝ) ≤ √(12630 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.383272776690 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12630 12630 (11 / 1000) ≤
    (0.008505598973 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12630) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.383272776690 : ℝ) ≤ √(12630 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12630)
  have hdiv : K / √(12630 : ℝ) ≤ K / 112.383272776690 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.383272776690 ≤ (0.008505598973 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12630.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12630 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12630 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12630 := gPlus_lower 12630
end BstLean.Part269.N12630

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12630
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035909191694 : ℝ) ≤ wn 12630 := by
  have hn : √(12630 : ℝ) ≤ 112.383272776691 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12630 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.383272776691 ≤ 2 / √(12630 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253301328 : ℝ) ≤ rhoBar 12630 BstLean.Part154.csC ∧
    rhoBar 12630 BstLean.Part154.csC ≤ 0.000253301720 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035909191694 : ℝ) / (1.295212 * 12630) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035909191695 : ℝ) / (1.29521 * 12630) := by gcongr
      _ ≤ (0.000253301720 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12630 BstLean.Part154.csC) ≤ 0.001013271042 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12630 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12630 BstLean.Part154.csC) (piBar (rhoBar 12630 BstLean.Part154.csC)) ≤ 0.000193473613 ∧
    cc1 (rhoBar 12630 BstLean.Part154.csC) (piBar (rhoBar 12630 BstLean.Part154.csC)) ≤ 0.000123108534 ∧
    cc2 (rhoBar 12630 BstLean.Part154.csC) ≤ 0.000071465435 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12630 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12630 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12630 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12630 BstLean.Part154.csC * nuR (rhoBar 12630 BstLean.Part154.csC)) ≤ 0.000506619481 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253301720 : ℝ) * 0.001013271042 := by gcongr
      _ ≤ (0.000506619481 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12630 BstLean.Part154.csC) * nuR (rhoBar 12630 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001013271042 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12630 BstLean.Part154.csC) * rhoBar 12630 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253301720 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253301720 / 2 + 0.399 * 0.001013271042 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193473613 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506619481 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123108534 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253301720 / 1.414213562 := by gcongr
      _ ≤ (0.000071465435 : ℝ) := by norm_num

end BstLean.Part269.N12630

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12630
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12630 BstLean.Part154.csC) (piBar (rhoBar 12630 BstLean.Part154.csC)) ≤ 1.61651E-7 := by
  have hr0 : 0 ≤ rhoBar 12630 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12630 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12630 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12630 BstLean.Part154.csC) (piBar (rhoBar 12630 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12630 BstLean.Part154.csC) (piBar (rhoBar 12630 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12630 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193473613 : ℝ) ^ 2 + 0.000123108534 ^ 2 + 3 * 0.000071465435 ^ 2 +
        2 * 0.797885 * 0.000193473613 * 0.000123108534 + 2 * 0.000193473613 * 0.000071465435 +
        4 * 0.797885 * 0.000123108534 * 0.000071465435 := by gcongr
    _ ≤ (1.61651E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12630 BstLean.Part154.csC Θ ≤ 0.002644372347 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12630 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12630 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12630 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12630 BstLean.Part154.csC) (piBar (rhoBar 12630 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12630 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035909191695 * 1.61651E-7 / (0.000253301328 : ℝ) := by gcongr
    _ ≤ 0.002644372347 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12630 BstLean.Part154.csC Θ ≤ 0.002934357441 + 0.000668190090 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12630 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12630 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12630 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035909191695 : ℝ) * ((2 * Θ * 0.000253301720 +
        (6863 / 10000) * 0.000253301720 * 12630 * 0.001013271042) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002934357441 + 0.000668190090 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12630 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12630 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12630 0.011 Θ ∧ gammaRatio 12630 0.011 Θ ≤ 0.000087078582 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12630 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035909191695 : ℝ) * 0.525 / ((1 - 0.011) * 12630) := by gcongr
      _ ≤ (0.000087078582 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12630 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12630 0.011 Θ) :=
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
    badAllowance 12630 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12630 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12630 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12630 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12630 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12630 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12630 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12630 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12630 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12630 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12630 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035909191695 : ℝ) * 12630 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12630 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003611063912 + 0.003312562437 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12630

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12630
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12630 BstLean.Part154.csC) (piBar (rhoBar 12630 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12630 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12630 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12630 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12630 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12630 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12630 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12630 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12630 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12630 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12630 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12630 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12630 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12630 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12630 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052631134581 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12630) ≤ 0.010626470929 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12630 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035909191695)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010626470929 + 2 * 0.737676 / 12630) := by gcongr
    _ ≤ (0.052631134581 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12630 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12630

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12630
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500385138 : ℝ) ≤ plow 12630 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12630) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052856759192)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388295483) : eMP 12630 0.011 xi bn ≤ 0.001195099580 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12630 : ℝ) * (1 - 0.011))) ≤ 0.000590902864 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001388295483 / (12630 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590902864 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590902864 : ℝ) + 3.141593 * 0.052856759192 / (12630 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001195099580 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052856759192)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388295483) : PiBarMP 12630 12 0.011 xi bn ≤ 0.161701890303 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12630 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037259837400 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.763455565761 : ℝ) ≤ √((12630 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.383272776690 : ℝ) ≤ √(12630 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12630) ≤ 0.123972259559 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037259837400 + 0.052856759192 * 1.772454 / (2 * (111.763455565761 : ℝ))) * (1 + 0.001195099580) +
        8 / (12630 * 112.383272776690) + 0.123972259559 := by gcongr
    _ ≤ (0.161701890303 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052856759192)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388295483) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282537113608) :
    parallelOracle 12630 0.011 xi bn cd ≤ 0.162698177627 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12630 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12630 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500385138 : ℝ) ≤ plow 12630 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.383272776690 : ℝ) ≤ √(12630 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282537113608 : ℝ) / (2 * 0.560500385138 * 112.383272776690)) * 0.161701890303 +
        0.282537113608 ^ 2 / (2 * 0.560500385138 * 112.383272776690) := by gcongr
    _ ≤ (0.162698177627 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052856759192) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388295483)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282537113608) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12630 12630 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500385138 : ℝ) ≤ plow 12630 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.383272776690 : ℝ) ≤ √(12630 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12630 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12630 Θ 1.22 ≤ 0.011799803185 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.383272776690 := by gcongr <;> linarith
      _ ≤ (0.011799803185 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12630 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12630 12630 0.011 ≤ 0.008505598973 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12630 12630 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12630 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12630 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12630 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12630 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162698177627 + 0.011799803185 + (0.008505598973 : ℝ) *
        (1 + 2 * (0.282537113608 + 0.011799803185) / (0.560500385138 * 112.383272776690))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12630]

end BstLean.Part269.N12630

/-! The original eight local profiles supply actual 12630 moment certificates. -/
namespace BstLean.Part269.N12630
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12630 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part253.group_scalar hg
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
      exact (mul_le_mul_of_nonneg_right (hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part253.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : NeededGroup g) :
    0 ≤ momentAllowance 12630 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12630 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052856759192 ∧
    0 ≤ bN 12630 BstLean.Part154.csC (groupTheta g) ∧ bN 12630 BstLean.Part154.csC (groupTheta g) ≤ 0.001388295483 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12630 12630 0.011
      (momentAllowance 12630 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12630 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12630 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12630 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12630 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12630 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229905979027 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12630 0.011
      (momentAllowance 12630 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12630 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12630
/-! The actual computed-centre upper energy formula at 12630. -/
namespace BstLean.Part269.N12630
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12630

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12630
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12630)
open BstLean.Part268 (cell12630)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085697116701
  | 2 => 0.086643728844
  | 3 => 0.087589054150
  | 4 => 0.088534642073
  | 5 => 0.089482362297
  | 6 => 0.090434451717
  | 7 => 0.091393565734
  | 8 => 0.092362833881
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12630 12630 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12630 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12630

/-! Actual upper energy certificates on all 43 source endpoints at 12630. -/
namespace BstLean.Part269.N12630
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12630)
open BstLean.Part268 (cell12630)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12630 (gMinus 12630) (1 - (cell12630 i).lower) ≤ 1 ∧
    energyUpper 12630 (gMinus 12630) (BstLean.Part211.gPlus 12630)
      (finiteEnergy 12630 12630 0.011) (1 - (cell12630 i).lower) ≤
      (cell12630 i).energy := by
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
  | ⟨10,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨10,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨11,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨12,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨13,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨14,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨15,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨16,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨17,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨18,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨19,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨20,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨21,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨22,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨23,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨24,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨25,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨26,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨27,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨28,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨29,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨30,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨31,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨32,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨33,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨34,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨35,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨36,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨37,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨38,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨39,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨40,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨41,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨42,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨43,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨44,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨45,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨46,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨47,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨48,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨49,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨50,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨51,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12630) (by norm_num)
        (q := 1 - (cell12630 ⟨52,by decide⟩).lower)
        (by norm_num [cell12630]) (by norm_num [cell12630])
      exact ⟨E.1,E.2.trans (by norm_num [cell12630])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12630

/-! Source-cell containment and simple scalar guards at 12630. -/
namespace BstLean.Part269.N12630
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12630)
open BstLean.Part268 (cell12630)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12630 ⟨10,by decide⟩).lower ∧ (cell12630 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12630 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12630 ⟨11,by decide⟩).lower ∧ (cell12630 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12630 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12630 ⟨12,by decide⟩).lower ∧ (cell12630 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12630 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12630 ⟨13,by decide⟩).lower ∧ (cell12630 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12630 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12630 ⟨14,by decide⟩).lower ∧ (cell12630 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12630 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12630 ⟨15,by decide⟩).lower ∧ (cell12630 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12630 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12630 ⟨16,by decide⟩).lower ∧ (cell12630 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12630 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12630 ⟨17,by decide⟩).lower ∧ (cell12630 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12630 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12630 ⟨18,by decide⟩).lower ∧ (cell12630 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12630 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12630 ⟨19,by decide⟩).lower ∧ (cell12630 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12630 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12630 ⟨20,by decide⟩).lower ∧ (cell12630 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12630 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12630 ⟨21,by decide⟩).lower ∧ (cell12630 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12630 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12630 ⟨22,by decide⟩).lower ∧ (cell12630 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12630 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12630 ⟨23,by decide⟩).lower ∧ (cell12630 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12630 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12630 ⟨24,by decide⟩).lower ∧ (cell12630 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12630 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12630 ⟨25,by decide⟩).lower ∧ (cell12630 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12630 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12630 ⟨26,by decide⟩).lower ∧ (cell12630 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12630 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12630 ⟨27,by decide⟩).lower ∧ (cell12630 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12630 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12630 ⟨28,by decide⟩).lower ∧ (cell12630 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12630 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12630 ⟨29,by decide⟩).lower ∧ (cell12630 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12630 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12630 ⟨30,by decide⟩).lower ∧ (cell12630 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12630 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12630 ⟨31,by decide⟩).lower ∧ (cell12630 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12630 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12630 ⟨32,by decide⟩).lower ∧ (cell12630 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12630 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12630 ⟨33,by decide⟩).lower ∧ (cell12630 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12630 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12630 ⟨34,by decide⟩).lower ∧ (cell12630 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12630 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12630 ⟨35,by decide⟩).lower ∧ (cell12630 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12630 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12630 ⟨36,by decide⟩).lower ∧ (cell12630 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12630 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12630 ⟨37,by decide⟩).lower ∧ (cell12630 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12630 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12630 ⟨38,by decide⟩).lower ∧ (cell12630 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12630 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12630 ⟨39,by decide⟩).lower ∧ (cell12630 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12630 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12630 ⟨40,by decide⟩).lower ∧ (cell12630 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12630 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12630 ⟨41,by decide⟩).lower ∧ (cell12630 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12630 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12630 ⟨42,by decide⟩).lower ∧ (cell12630 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12630 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12630 ⟨43,by decide⟩).lower ∧ (cell12630 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12630 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12630 ⟨44,by decide⟩).lower ∧ (cell12630 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12630 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12630 ⟨45,by decide⟩).lower ∧ (cell12630 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12630 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12630 ⟨46,by decide⟩).lower ∧ (cell12630 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12630 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12630 ⟨47,by decide⟩).lower ∧ (cell12630 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12630 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12630 ⟨48,by decide⟩).lower ∧ (cell12630 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12630 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12630 ⟨49,by decide⟩).lower ∧ (cell12630 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12630 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12630 ⟨50,by decide⟩).lower ∧ (cell12630 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12630 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12630 ⟨51,by decide⟩).lower ∧ (cell12630 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12630 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12630 ⟨52,by decide⟩).lower ∧ (cell12630 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12630 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12630 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12630 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12630,cell12630,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12630 i).lower ∧
    (cell12630 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12630 i).upper ≤ (0.532 : ℝ) ∧
    (cell12630 i).centre ≤ (0.1 : ℝ) ∧ (cell12630 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12630 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12630 i).centre = pilotGroupCentre (centreGroup i) := by
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
  | ⟨10,h⟩ => exact pilot_sourceCell10
  | ⟨11,h⟩ => exact pilot_sourceCell11
  | ⟨12,h⟩ => exact pilot_sourceCell12
  | ⟨13,h⟩ => exact pilot_sourceCell13
  | ⟨14,h⟩ => exact pilot_sourceCell14
  | ⟨15,h⟩ => exact pilot_sourceCell15
  | ⟨16,h⟩ => exact pilot_sourceCell16
  | ⟨17,h⟩ => exact pilot_sourceCell17
  | ⟨18,h⟩ => exact pilot_sourceCell18
  | ⟨19,h⟩ => exact pilot_sourceCell19
  | ⟨20,h⟩ => exact pilot_sourceCell20
  | ⟨21,h⟩ => exact pilot_sourceCell21
  | ⟨22,h⟩ => exact pilot_sourceCell22
  | ⟨23,h⟩ => exact pilot_sourceCell23
  | ⟨24,h⟩ => exact pilot_sourceCell24
  | ⟨25,h⟩ => exact pilot_sourceCell25
  | ⟨26,h⟩ => exact pilot_sourceCell26
  | ⟨27,h⟩ => exact pilot_sourceCell27
  | ⟨28,h⟩ => exact pilot_sourceCell28
  | ⟨29,h⟩ => exact pilot_sourceCell29
  | ⟨30,h⟩ => exact pilot_sourceCell30
  | ⟨31,h⟩ => exact pilot_sourceCell31
  | ⟨32,h⟩ => exact pilot_sourceCell32
  | ⟨33,h⟩ => exact pilot_sourceCell33
  | ⟨34,h⟩ => exact pilot_sourceCell34
  | ⟨35,h⟩ => exact pilot_sourceCell35
  | ⟨36,h⟩ => exact pilot_sourceCell36
  | ⟨37,h⟩ => exact pilot_sourceCell37
  | ⟨38,h⟩ => exact pilot_sourceCell38
  | ⟨39,h⟩ => exact pilot_sourceCell39
  | ⟨40,h⟩ => exact pilot_sourceCell40
  | ⟨41,h⟩ => exact pilot_sourceCell41
  | ⟨42,h⟩ => exact pilot_sourceCell42
  | ⟨43,h⟩ => exact pilot_sourceCell43
  | ⟨44,h⟩ => exact pilot_sourceCell44
  | ⟨45,h⟩ => exact pilot_sourceCell45
  | ⟨46,h⟩ => exact pilot_sourceCell46
  | ⟨47,h⟩ => exact pilot_sourceCell47
  | ⟨48,h⟩ => exact pilot_sourceCell48
  | ⟨49,h⟩ => exact pilot_sourceCell49
  | ⟨50,h⟩ => exact pilot_sourceCell50
  | ⟨51,h⟩ => exact pilot_sourceCell51
  | ⟨52,h⟩ => exact pilot_sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12630

/-! The local source numeric instances at 12630 have no network premises. -/
namespace BstLean.Part269.N12630
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12630)
open BstLean.Part268 (cell12630)

noncomputable def sourceNumerics12630 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12630 (cell12630 i)
      scalarRow12630.M scalarRow12630.H scalarRow12630.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := pilot_source_cell hi
  have E := pilot_upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := centreCertificate_from_moment (by norm_num)
      (G.window.2.trans (by norm_num)) (pilot_groupMomentCertificate hg)
      hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
    energy_allowance := scalarRow12630.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12630]
    centre_nonneg := (scalarRow12630.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12630])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12630
/-! Actual 12631 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12631
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12631 ≤ (1.035907757660 : ℝ) := by
  have hr : (112.387721749308 : ℝ) ≤ √(12631 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.387721749308 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12631 12631 (11 / 1000) ≤
    (0.008505262268 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12631) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.387721749308 : ℝ) ≤ √(12631 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12631)
  have hdiv : K / √(12631 : ℝ) ≤ K / 112.387721749308 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.387721749308 ≤ (0.008505262268 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12631.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12631 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12631 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12631 := gPlus_lower 12631
end BstLean.Part269.N12631

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12631
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035907757659 : ℝ) ≤ wn 12631 := by
  have hn : √(12631 : ℝ) ≤ 112.387721749309 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12631 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.387721749309 ≤ 2 / √(12631 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253280924 : ℝ) ≤ rhoBar 12631 BstLean.Part154.csC ∧
    rhoBar 12631 BstLean.Part154.csC ≤ 0.000253281316 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035907757659 : ℝ) / (1.295212 * 12631) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035907757660 : ℝ) / (1.29521 * 12631) := by gcongr
      _ ≤ (0.000253281316 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12631 BstLean.Part154.csC) ≤ 0.001013189416 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12631 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12631 BstLean.Part154.csC) (piBar (rhoBar 12631 BstLean.Part154.csC)) ≤ 0.000193458028 ∧
    cc1 (rhoBar 12631 BstLean.Part154.csC) (piBar (rhoBar 12631 BstLean.Part154.csC)) ≤ 0.000123098617 ∧
    cc2 (rhoBar 12631 BstLean.Part154.csC) ≤ 0.000071459678 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12631 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12631 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12631 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12631 BstLean.Part154.csC * nuR (rhoBar 12631 BstLean.Part154.csC)) ≤ 0.000506578670 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253281316 : ℝ) * 0.001013189416 := by gcongr
      _ ≤ (0.000506578670 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12631 BstLean.Part154.csC) * nuR (rhoBar 12631 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001013189416 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12631 BstLean.Part154.csC) * rhoBar 12631 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253281316 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253281316 / 2 + 0.399 * 0.001013189416 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193458028 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506578670 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123098617 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253281316 / 1.414213562 := by gcongr
      _ ≤ (0.000071459678 : ℝ) := by norm_num

end BstLean.Part269.N12631

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12631
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12631 BstLean.Part154.csC) (piBar (rhoBar 12631 BstLean.Part154.csC)) ≤ 1.61625E-7 := by
  have hr0 : 0 ≤ rhoBar 12631 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12631 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12631 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12631 BstLean.Part154.csC) (piBar (rhoBar 12631 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12631 BstLean.Part154.csC) (piBar (rhoBar 12631 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12631 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193458028 : ℝ) ^ 2 + 0.000123098617 ^ 2 + 3 * 0.000071459678 ^ 2 +
        2 * 0.797885 * 0.000193458028 * 0.000123098617 + 2 * 0.000193458028 * 0.000071459678 +
        4 * 0.797885 * 0.000123098617 * 0.000071459678 := by gcongr
    _ ≤ (1.61625E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12631 BstLean.Part154.csC Θ ≤ 0.002644156358 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12631 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12631 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12631 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12631 BstLean.Part154.csC) (piBar (rhoBar 12631 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12631 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035907757660 * 1.61625E-7 / (0.000253280924 : ℝ) := by gcongr
    _ ≤ 0.002644156358 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12631 BstLean.Part154.csC Θ ≤ 0.002934112942 + 0.000668135341 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12631 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12631 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12631 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035907757660 : ℝ) * ((2 * Θ * 0.000253281316 +
        (6863 / 10000) * 0.000253281316 * 12631 * 0.001013189416) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002934112942 + 0.000668135341 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12631 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12631 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12631 0.011 Θ ∧ gammaRatio 12631 0.011 Θ ≤ 0.000087071567 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12631 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035907757660 : ℝ) * 0.525 / ((1 - 0.011) * 12631) := by gcongr
      _ ≤ (0.000087071567 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12631 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12631 0.011 Θ) :=
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
    badAllowance 12631 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12631 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12631 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12631 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12631 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12631 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12631 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12631 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12631 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12631 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12631 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035907757660 : ℝ) * 12631 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12631 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003610819413 + 0.003312291699 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12631

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12631
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12631 BstLean.Part154.csC) (piBar (rhoBar 12631 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12631 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12631 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12631 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12631 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12631 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12631 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12631 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12631 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12631 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12631 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12631 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12631 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12631 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12631 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052629028479 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12631) ≤ 0.010626050271 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12631 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035907757660)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010626050271 + 2 * 0.737676 / 12631) := by gcongr
    _ ≤ (0.052629028479 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12631 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12631

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12631
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500430860 : ℝ) ≤ plow 12631 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12631) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052856372555)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388182088) : eMP 12631 0.011 xi bn ≤ 0.001195003384 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12631 : ℝ) * (1 - 0.011))) ≤ 0.000590855341 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001388182088 / (12631 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590855341 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590855341 : ℝ) + 3.141593 * 0.052856372555 / (12631 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001195003384 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052856372555)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388182088) : PiBarMP 12631 12 0.011 xi bn ≤ 0.161695435243 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12631 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037258315690 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.767880001367 : ℝ) ≤ √((12631 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.387721749308 : ℝ) ≤ √(12631 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12631) ≤ 0.123967352002 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037258315690 + 0.052856372555 * 1.772454 / (2 * (111.767880001367 : ℝ))) * (1 + 0.001195003384) +
        8 / (12631 * 112.387721749308) + 0.123967352002 := by gcongr
    _ ≤ (0.161695435243 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052856372555)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388182088) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282534166645) :
    parallelOracle 12631 0.011 xi bn cd ≤ 0.162691651571 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12631 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12631 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500430860 : ℝ) ≤ plow 12631 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.387721749308 : ℝ) ≤ √(12631 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282534166645 : ℝ) / (2 * 0.560500430860 * 112.387721749308)) * 0.161695435243 +
        0.282534166645 ^ 2 / (2 * 0.560500430860 * 112.387721749308) := by gcongr
    _ ≤ (0.162691651571 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052856372555) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388182088)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282534166645) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12631 12631 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500430860 : ℝ) ≤ plow 12631 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.387721749308 : ℝ) ≤ √(12631 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12631 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12631 Θ 1.22 ≤ 0.011799336079 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.387721749308 := by gcongr <;> linarith
      _ ≤ (0.011799336079 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12631 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12631 12631 0.011 ≤ 0.008505262268 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12631 12631 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12631 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12631 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12631 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12631 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162691651571 + 0.011799336079 + (0.008505262268 : ℝ) *
        (1 + 2 * (0.282534166645 + 0.011799336079) / (0.560500430860 * 112.387721749308))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12631]

end BstLean.Part269.N12631

/-! The original eight local profiles supply actual 12631 moment certificates. -/
namespace BstLean.Part269.N12631
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12631 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part253.group_scalar hg
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
      exact (mul_le_mul_of_nonneg_right (hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part253.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : NeededGroup g) :
    0 ≤ momentAllowance 12631 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12631 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052856372555 ∧
    0 ≤ bN 12631 BstLean.Part154.csC (groupTheta g) ∧ bN 12631 BstLean.Part154.csC (groupTheta g) ≤ 0.001388182088 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12631 12631 0.011
      (momentAllowance 12631 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12631 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12631 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12631 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12631 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12631 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229905138166 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12631 0.011
      (momentAllowance 12631 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12631 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12631
/-! The actual computed-centre upper energy formula at 12631. -/
namespace BstLean.Part269.N12631
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12631

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12631
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12631)
open BstLean.Part268 (cell12631)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085694122340
  | 2 => 0.086640677668
  | 3 => 0.087585937583
  | 4 => 0.088531449585
  | 5 => 0.089479081061
  | 6 => 0.090431066229
  | 7 => 0.091390057382
  | 8 => 0.092359180475
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12631 12631 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12631 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12631

/-! Actual upper energy certificates on all 43 source endpoints at 12631. -/
namespace BstLean.Part269.N12631
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12631)
open BstLean.Part268 (cell12631)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12631 (gMinus 12631) (1 - (cell12631 i).lower) ≤ 1 ∧
    energyUpper 12631 (gMinus 12631) (BstLean.Part211.gPlus 12631)
      (finiteEnergy 12631 12631 0.011) (1 - (cell12631 i).lower) ≤
      (cell12631 i).energy := by
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
  | ⟨10,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨10,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨11,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨12,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨13,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨14,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨15,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨16,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨17,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨18,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨19,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨20,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨21,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨22,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨23,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨24,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨25,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨26,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨27,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨28,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨29,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨30,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨31,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨32,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨33,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨34,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨35,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨36,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨37,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨38,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨39,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨40,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨41,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨42,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨43,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨44,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨45,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨46,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨47,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨48,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨49,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨50,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨51,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12631) (by norm_num)
        (q := 1 - (cell12631 ⟨52,by decide⟩).lower)
        (by norm_num [cell12631]) (by norm_num [cell12631])
      exact ⟨E.1,E.2.trans (by norm_num [cell12631])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12631

/-! Source-cell containment and simple scalar guards at 12631. -/
namespace BstLean.Part269.N12631
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12631)
open BstLean.Part268 (cell12631)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12631 ⟨10,by decide⟩).lower ∧ (cell12631 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12631 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12631 ⟨11,by decide⟩).lower ∧ (cell12631 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12631 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12631 ⟨12,by decide⟩).lower ∧ (cell12631 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12631 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12631 ⟨13,by decide⟩).lower ∧ (cell12631 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12631 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12631 ⟨14,by decide⟩).lower ∧ (cell12631 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12631 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12631 ⟨15,by decide⟩).lower ∧ (cell12631 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12631 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12631 ⟨16,by decide⟩).lower ∧ (cell12631 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12631 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12631 ⟨17,by decide⟩).lower ∧ (cell12631 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12631 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12631 ⟨18,by decide⟩).lower ∧ (cell12631 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12631 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12631 ⟨19,by decide⟩).lower ∧ (cell12631 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12631 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12631 ⟨20,by decide⟩).lower ∧ (cell12631 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12631 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12631 ⟨21,by decide⟩).lower ∧ (cell12631 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12631 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12631 ⟨22,by decide⟩).lower ∧ (cell12631 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12631 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12631 ⟨23,by decide⟩).lower ∧ (cell12631 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12631 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12631 ⟨24,by decide⟩).lower ∧ (cell12631 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12631 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12631 ⟨25,by decide⟩).lower ∧ (cell12631 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12631 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12631 ⟨26,by decide⟩).lower ∧ (cell12631 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12631 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12631 ⟨27,by decide⟩).lower ∧ (cell12631 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12631 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12631 ⟨28,by decide⟩).lower ∧ (cell12631 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12631 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12631 ⟨29,by decide⟩).lower ∧ (cell12631 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12631 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12631 ⟨30,by decide⟩).lower ∧ (cell12631 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12631 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12631 ⟨31,by decide⟩).lower ∧ (cell12631 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12631 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12631 ⟨32,by decide⟩).lower ∧ (cell12631 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12631 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12631 ⟨33,by decide⟩).lower ∧ (cell12631 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12631 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12631 ⟨34,by decide⟩).lower ∧ (cell12631 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12631 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12631 ⟨35,by decide⟩).lower ∧ (cell12631 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12631 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12631 ⟨36,by decide⟩).lower ∧ (cell12631 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12631 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12631 ⟨37,by decide⟩).lower ∧ (cell12631 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12631 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12631 ⟨38,by decide⟩).lower ∧ (cell12631 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12631 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12631 ⟨39,by decide⟩).lower ∧ (cell12631 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12631 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12631 ⟨40,by decide⟩).lower ∧ (cell12631 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12631 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12631 ⟨41,by decide⟩).lower ∧ (cell12631 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12631 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12631 ⟨42,by decide⟩).lower ∧ (cell12631 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12631 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12631 ⟨43,by decide⟩).lower ∧ (cell12631 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12631 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12631 ⟨44,by decide⟩).lower ∧ (cell12631 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12631 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12631 ⟨45,by decide⟩).lower ∧ (cell12631 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12631 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12631 ⟨46,by decide⟩).lower ∧ (cell12631 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12631 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12631 ⟨47,by decide⟩).lower ∧ (cell12631 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12631 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12631 ⟨48,by decide⟩).lower ∧ (cell12631 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12631 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12631 ⟨49,by decide⟩).lower ∧ (cell12631 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12631 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12631 ⟨50,by decide⟩).lower ∧ (cell12631 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12631 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12631 ⟨51,by decide⟩).lower ∧ (cell12631 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12631 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12631 ⟨52,by decide⟩).lower ∧ (cell12631 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12631 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12631 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12631 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12631,cell12631,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12631 i).lower ∧
    (cell12631 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12631 i).upper ≤ (0.532 : ℝ) ∧
    (cell12631 i).centre ≤ (0.1 : ℝ) ∧ (cell12631 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12631 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12631 i).centre = pilotGroupCentre (centreGroup i) := by
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
  | ⟨10,h⟩ => exact pilot_sourceCell10
  | ⟨11,h⟩ => exact pilot_sourceCell11
  | ⟨12,h⟩ => exact pilot_sourceCell12
  | ⟨13,h⟩ => exact pilot_sourceCell13
  | ⟨14,h⟩ => exact pilot_sourceCell14
  | ⟨15,h⟩ => exact pilot_sourceCell15
  | ⟨16,h⟩ => exact pilot_sourceCell16
  | ⟨17,h⟩ => exact pilot_sourceCell17
  | ⟨18,h⟩ => exact pilot_sourceCell18
  | ⟨19,h⟩ => exact pilot_sourceCell19
  | ⟨20,h⟩ => exact pilot_sourceCell20
  | ⟨21,h⟩ => exact pilot_sourceCell21
  | ⟨22,h⟩ => exact pilot_sourceCell22
  | ⟨23,h⟩ => exact pilot_sourceCell23
  | ⟨24,h⟩ => exact pilot_sourceCell24
  | ⟨25,h⟩ => exact pilot_sourceCell25
  | ⟨26,h⟩ => exact pilot_sourceCell26
  | ⟨27,h⟩ => exact pilot_sourceCell27
  | ⟨28,h⟩ => exact pilot_sourceCell28
  | ⟨29,h⟩ => exact pilot_sourceCell29
  | ⟨30,h⟩ => exact pilot_sourceCell30
  | ⟨31,h⟩ => exact pilot_sourceCell31
  | ⟨32,h⟩ => exact pilot_sourceCell32
  | ⟨33,h⟩ => exact pilot_sourceCell33
  | ⟨34,h⟩ => exact pilot_sourceCell34
  | ⟨35,h⟩ => exact pilot_sourceCell35
  | ⟨36,h⟩ => exact pilot_sourceCell36
  | ⟨37,h⟩ => exact pilot_sourceCell37
  | ⟨38,h⟩ => exact pilot_sourceCell38
  | ⟨39,h⟩ => exact pilot_sourceCell39
  | ⟨40,h⟩ => exact pilot_sourceCell40
  | ⟨41,h⟩ => exact pilot_sourceCell41
  | ⟨42,h⟩ => exact pilot_sourceCell42
  | ⟨43,h⟩ => exact pilot_sourceCell43
  | ⟨44,h⟩ => exact pilot_sourceCell44
  | ⟨45,h⟩ => exact pilot_sourceCell45
  | ⟨46,h⟩ => exact pilot_sourceCell46
  | ⟨47,h⟩ => exact pilot_sourceCell47
  | ⟨48,h⟩ => exact pilot_sourceCell48
  | ⟨49,h⟩ => exact pilot_sourceCell49
  | ⟨50,h⟩ => exact pilot_sourceCell50
  | ⟨51,h⟩ => exact pilot_sourceCell51
  | ⟨52,h⟩ => exact pilot_sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12631

/-! The local source numeric instances at 12631 have no network premises. -/
namespace BstLean.Part269.N12631
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12631)
open BstLean.Part268 (cell12631)

noncomputable def sourceNumerics12631 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12631 (cell12631 i)
      scalarRow12631.M scalarRow12631.H scalarRow12631.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := pilot_source_cell hi
  have E := pilot_upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := centreCertificate_from_moment (by norm_num)
      (G.window.2.trans (by norm_num)) (pilot_groupMomentCertificate hg)
      hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
    energy_allowance := scalarRow12631.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12631]
    centre_nonneg := (scalarRow12631.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12631])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12631
/-! Actual 12632 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12632
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12632 ≤ (1.035906323796 : ℝ) := by
  have hr : (112.392170545816 : ℝ) ≤ √(12632 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.392170545816 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12632 12632 (11 / 1000) ≤
    (0.008504925603 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12632) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.392170545816 : ℝ) ≤ √(12632 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12632)
  have hdiv : K / √(12632 : ℝ) ≤ K / 112.392170545816 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.392170545816 ≤ (0.008504925603 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12632.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12632 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12632 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12632 := gPlus_lower 12632
end BstLean.Part269.N12632

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12632
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035906323795 : ℝ) ≤ wn 12632 := by
  have hn : √(12632 : ℝ) ≤ 112.392170545817 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12632 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.392170545817 ≤ 2 / √(12632 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253260522 : ℝ) ≤ rhoBar 12632 BstLean.Part154.csC ∧
    rhoBar 12632 BstLean.Part154.csC ≤ 0.000253260914 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035906323795 : ℝ) / (1.295212 * 12632) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035906323796 : ℝ) / (1.29521 * 12632) := by gcongr
      _ ≤ (0.000253260914 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12632 BstLean.Part154.csC) ≤ 0.001013107798 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12632 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12632 BstLean.Part154.csC) (piBar (rhoBar 12632 BstLean.Part154.csC)) ≤ 0.000193442444 ∧
    cc1 (rhoBar 12632 BstLean.Part154.csC) (piBar (rhoBar 12632 BstLean.Part154.csC)) ≤ 0.000123088701 ∧
    cc2 (rhoBar 12632 BstLean.Part154.csC) ≤ 0.000071453922 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12632 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12632 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12632 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12632 BstLean.Part154.csC * nuR (rhoBar 12632 BstLean.Part154.csC)) ≤ 0.000506537864 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253260914 : ℝ) * 0.001013107798 := by gcongr
      _ ≤ (0.000506537864 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12632 BstLean.Part154.csC) * nuR (rhoBar 12632 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001013107798 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12632 BstLean.Part154.csC) * rhoBar 12632 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253260914 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253260914 / 2 + 0.399 * 0.001013107798 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193442444 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506537864 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123088701 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253260914 / 1.414213562 := by gcongr
      _ ≤ (0.000071453922 : ℝ) := by norm_num

end BstLean.Part269.N12632

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12632
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12632 BstLean.Part154.csC) (piBar (rhoBar 12632 BstLean.Part154.csC)) ≤ 1.61599E-7 := by
  have hr0 : 0 ≤ rhoBar 12632 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12632 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12632 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12632 BstLean.Part154.csC) (piBar (rhoBar 12632 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12632 BstLean.Part154.csC) (piBar (rhoBar 12632 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12632 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193442444 : ℝ) ^ 2 + 0.000123088701 ^ 2 + 3 * 0.000071453922 ^ 2 +
        2 * 0.797885 * 0.000193442444 * 0.000123088701 + 2 * 0.000193442444 * 0.000071453922 +
        4 * 0.797885 * 0.000123088701 * 0.000071453922 := by gcongr
    _ ≤ (1.61599E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12632 BstLean.Part154.csC Θ ≤ 0.002643940315 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12632 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12632 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12632 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12632 BstLean.Part154.csC) (piBar (rhoBar 12632 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12632 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035906323796 * 1.61599E-7 / (0.000253260522 : ℝ) := by gcongr
    _ ≤ 0.002643940315 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12632 BstLean.Part154.csC Θ ≤ 0.002933868453 + 0.000668080598 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12632 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12632 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12632 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035906323796 : ℝ) * ((2 * Θ * 0.000253260914 +
        (6863 / 10000) * 0.000253260914 * 12632 * 0.001013107798) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002933868453 + 0.000668080598 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12632 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12632 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12632 0.011 Θ ∧ gammaRatio 12632 0.011 Θ ≤ 0.000087064554 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12632 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035906323796 : ℝ) * 0.525 / ((1 - 0.011) * 12632) := by gcongr
      _ ≤ (0.000087064554 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12632 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12632 0.011 Θ) :=
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
    badAllowance 12632 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12632 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12632 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12632 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12632 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12632 0.011 Θ) 1.12 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 1 (gammaRatio 12632 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12632 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12632 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12632 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12632 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035906323796 : ℝ) * 12632 *
        (2.5110E-8 / 1.1045361 + 3.0670E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12632 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003610574924 + 0.003312020913 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12632

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12632
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12632 BstLean.Part154.csC) (piBar (rhoBar 12632 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12632 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12632 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12632 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12632 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12632 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12632 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12632 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12632 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12632 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12632 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12632 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12632 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12632 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12632 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052626922625 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12632) ≤ 0.010625629662 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12632 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035906323796)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010625629662 + 2 * 0.737676 / 12632) := by gcongr
    _ ≤ (0.052626922625 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12632 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12632

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12632
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500476575 : ℝ) ≤ plow 12632 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12632) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052855985904)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388068666) : eMP 12632 0.011 xi bn ≤ 0.001194907182 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12632 : ℝ) * (1 - 0.011))) ≤ 0.000590807815 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001388068666 / (12632 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590807815 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590807815 : ℝ) + 3.141593 * 0.052855985904 / (12632 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001194907182 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052855985904)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388068666) : PiBarMP 12632 12 0.011 xi bn ≤ 0.161688980343 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12632 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037256793556 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.772304261834 : ℝ) ≤ √((12632 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.392170545816 : ℝ) ≤ √(12632 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12632) ≤ 0.123962445028 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037256793556 + 0.052855985904 * 1.772454 / (2 * (111.772304261834 : ℝ))) * (1 + 0.001194907182) +
        8 / (12632 * 112.392170545816) + 0.123962445028 := by gcongr
    _ ≤ (0.161688980343 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052855985904)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388068666) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282531219897) :
    parallelOracle 12632 0.011 xi bn cd ≤ 0.162685125684 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12632 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12632 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500476575 : ℝ) ≤ plow 12632 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.392170545816 : ℝ) ≤ √(12632 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282531219897 : ℝ) / (2 * 0.560500476575 * 112.392170545816)) * 0.161688980343 +
        0.282531219897 ^ 2 / (2 * 0.560500476575 * 112.392170545816) := by gcongr
    _ ≤ (0.162685125684 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052855985904) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001388068666)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282531219897) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12632 12632 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500476575 : ℝ) ≤ plow 12632 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.392170545816 : ℝ) ≤ √(12632 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12632 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12632 Θ 1.22 ≤ 0.011798869028 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.392170545816 := by gcongr <;> linarith
      _ ≤ (0.011798869028 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12632 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12632 12632 0.011 ≤ 0.008504925603 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12632 12632 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12632 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12632 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12632 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12632 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162685125684 + 0.011798869028 + (0.008504925603 : ℝ) *
        (1 + 2 * (0.282531219897 + 0.011798869028) / (0.560500476575 * 112.392170545816))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12632]

end BstLean.Part269.N12632

/-! The original eight local profiles supply actual 12632 moment certificates. -/
namespace BstLean.Part269.N12632
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12632 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part253.group_scalar hg
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
      exact (mul_le_mul_of_nonneg_right (hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part253.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : NeededGroup g) :
    0 ≤ momentAllowance 12632 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12632 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052855985904 ∧
    0 ≤ bN 12632 BstLean.Part154.csC (groupTheta g) ∧ bN 12632 BstLean.Part154.csC (groupTheta g) ≤ 0.001388068666 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12632 12632 0.011
      (momentAllowance 12632 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12632 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12632 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12632 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12632 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12632 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229904297272 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12632 0.011
      (momentAllowance 12632 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12632 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12632
/-! The actual computed-centre upper energy formula at 12632. -/
namespace BstLean.Part269.N12632
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12632

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12632
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12632)
open BstLean.Part268 (cell12632)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085691129142
  | 2 => 0.086637627704
  | 3 => 0.087582822288
  | 4 => 0.088528258442
  | 5 => 0.089475801261
  | 6 => 0.090427682286
  | 7 => 0.091386550708
  | 8 => 0.092355528907
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12632 12632 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12632 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12632

/-! Actual upper energy certificates on all 43 source endpoints at 12632. -/
namespace BstLean.Part269.N12632
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12632)
open BstLean.Part268 (cell12632)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12632 (gMinus 12632) (1 - (cell12632 i).lower) ≤ 1 ∧
    energyUpper 12632 (gMinus 12632) (BstLean.Part211.gPlus 12632)
      (finiteEnergy 12632 12632 0.011) (1 - (cell12632 i).lower) ≤
      (cell12632 i).energy := by
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
  | ⟨10,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨10,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨11,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨12,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨13,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨14,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨15,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨16,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨17,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨18,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨19,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨20,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨21,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨22,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨23,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨24,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨25,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨26,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨27,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨28,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨29,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨30,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨31,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨32,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨33,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨34,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨35,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨36,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨37,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨38,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨39,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨40,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨41,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨42,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨43,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨44,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨45,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨46,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨47,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨48,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨49,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨50,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨51,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12632) (by norm_num)
        (q := 1 - (cell12632 ⟨52,by decide⟩).lower)
        (by norm_num [cell12632]) (by norm_num [cell12632])
      exact ⟨E.1,E.2.trans (by norm_num [cell12632])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12632

/-! Source-cell containment and simple scalar guards at 12632. -/
namespace BstLean.Part269.N12632
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12632)
open BstLean.Part268 (cell12632)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12632 ⟨10,by decide⟩).lower ∧ (cell12632 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12632 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12632 ⟨11,by decide⟩).lower ∧ (cell12632 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12632 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12632 ⟨12,by decide⟩).lower ∧ (cell12632 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12632 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12632 ⟨13,by decide⟩).lower ∧ (cell12632 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12632 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12632 ⟨14,by decide⟩).lower ∧ (cell12632 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12632 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12632 ⟨15,by decide⟩).lower ∧ (cell12632 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12632 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12632 ⟨16,by decide⟩).lower ∧ (cell12632 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12632 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12632 ⟨17,by decide⟩).lower ∧ (cell12632 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12632 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12632 ⟨18,by decide⟩).lower ∧ (cell12632 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12632 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12632 ⟨19,by decide⟩).lower ∧ (cell12632 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12632 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12632 ⟨20,by decide⟩).lower ∧ (cell12632 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12632 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12632 ⟨21,by decide⟩).lower ∧ (cell12632 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12632 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12632 ⟨22,by decide⟩).lower ∧ (cell12632 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12632 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12632 ⟨23,by decide⟩).lower ∧ (cell12632 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12632 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12632 ⟨24,by decide⟩).lower ∧ (cell12632 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12632 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12632 ⟨25,by decide⟩).lower ∧ (cell12632 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12632 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12632 ⟨26,by decide⟩).lower ∧ (cell12632 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12632 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12632 ⟨27,by decide⟩).lower ∧ (cell12632 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12632 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12632 ⟨28,by decide⟩).lower ∧ (cell12632 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12632 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12632 ⟨29,by decide⟩).lower ∧ (cell12632 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12632 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12632 ⟨30,by decide⟩).lower ∧ (cell12632 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12632 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12632 ⟨31,by decide⟩).lower ∧ (cell12632 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12632 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12632 ⟨32,by decide⟩).lower ∧ (cell12632 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12632 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12632 ⟨33,by decide⟩).lower ∧ (cell12632 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12632 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12632 ⟨34,by decide⟩).lower ∧ (cell12632 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12632 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12632 ⟨35,by decide⟩).lower ∧ (cell12632 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12632 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12632 ⟨36,by decide⟩).lower ∧ (cell12632 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12632 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12632 ⟨37,by decide⟩).lower ∧ (cell12632 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12632 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12632 ⟨38,by decide⟩).lower ∧ (cell12632 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12632 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12632 ⟨39,by decide⟩).lower ∧ (cell12632 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12632 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12632 ⟨40,by decide⟩).lower ∧ (cell12632 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12632 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12632 ⟨41,by decide⟩).lower ∧ (cell12632 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12632 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12632 ⟨42,by decide⟩).lower ∧ (cell12632 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12632 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12632 ⟨43,by decide⟩).lower ∧ (cell12632 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12632 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12632 ⟨44,by decide⟩).lower ∧ (cell12632 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12632 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12632 ⟨45,by decide⟩).lower ∧ (cell12632 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12632 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12632 ⟨46,by decide⟩).lower ∧ (cell12632 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12632 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12632 ⟨47,by decide⟩).lower ∧ (cell12632 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12632 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12632 ⟨48,by decide⟩).lower ∧ (cell12632 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12632 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12632 ⟨49,by decide⟩).lower ∧ (cell12632 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12632 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12632 ⟨50,by decide⟩).lower ∧ (cell12632 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12632 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12632 ⟨51,by decide⟩).lower ∧ (cell12632 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12632 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12632 ⟨52,by decide⟩).lower ∧ (cell12632 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12632 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12632 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12632 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12632,cell12632,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12632 i).lower ∧
    (cell12632 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12632 i).upper ≤ (0.532 : ℝ) ∧
    (cell12632 i).centre ≤ (0.1 : ℝ) ∧ (cell12632 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12632 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12632 i).centre = pilotGroupCentre (centreGroup i) := by
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
  | ⟨10,h⟩ => exact pilot_sourceCell10
  | ⟨11,h⟩ => exact pilot_sourceCell11
  | ⟨12,h⟩ => exact pilot_sourceCell12
  | ⟨13,h⟩ => exact pilot_sourceCell13
  | ⟨14,h⟩ => exact pilot_sourceCell14
  | ⟨15,h⟩ => exact pilot_sourceCell15
  | ⟨16,h⟩ => exact pilot_sourceCell16
  | ⟨17,h⟩ => exact pilot_sourceCell17
  | ⟨18,h⟩ => exact pilot_sourceCell18
  | ⟨19,h⟩ => exact pilot_sourceCell19
  | ⟨20,h⟩ => exact pilot_sourceCell20
  | ⟨21,h⟩ => exact pilot_sourceCell21
  | ⟨22,h⟩ => exact pilot_sourceCell22
  | ⟨23,h⟩ => exact pilot_sourceCell23
  | ⟨24,h⟩ => exact pilot_sourceCell24
  | ⟨25,h⟩ => exact pilot_sourceCell25
  | ⟨26,h⟩ => exact pilot_sourceCell26
  | ⟨27,h⟩ => exact pilot_sourceCell27
  | ⟨28,h⟩ => exact pilot_sourceCell28
  | ⟨29,h⟩ => exact pilot_sourceCell29
  | ⟨30,h⟩ => exact pilot_sourceCell30
  | ⟨31,h⟩ => exact pilot_sourceCell31
  | ⟨32,h⟩ => exact pilot_sourceCell32
  | ⟨33,h⟩ => exact pilot_sourceCell33
  | ⟨34,h⟩ => exact pilot_sourceCell34
  | ⟨35,h⟩ => exact pilot_sourceCell35
  | ⟨36,h⟩ => exact pilot_sourceCell36
  | ⟨37,h⟩ => exact pilot_sourceCell37
  | ⟨38,h⟩ => exact pilot_sourceCell38
  | ⟨39,h⟩ => exact pilot_sourceCell39
  | ⟨40,h⟩ => exact pilot_sourceCell40
  | ⟨41,h⟩ => exact pilot_sourceCell41
  | ⟨42,h⟩ => exact pilot_sourceCell42
  | ⟨43,h⟩ => exact pilot_sourceCell43
  | ⟨44,h⟩ => exact pilot_sourceCell44
  | ⟨45,h⟩ => exact pilot_sourceCell45
  | ⟨46,h⟩ => exact pilot_sourceCell46
  | ⟨47,h⟩ => exact pilot_sourceCell47
  | ⟨48,h⟩ => exact pilot_sourceCell48
  | ⟨49,h⟩ => exact pilot_sourceCell49
  | ⟨50,h⟩ => exact pilot_sourceCell50
  | ⟨51,h⟩ => exact pilot_sourceCell51
  | ⟨52,h⟩ => exact pilot_sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12632

/-! The local source numeric instances at 12632 have no network premises. -/
namespace BstLean.Part269.N12632
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12632)
open BstLean.Part268 (cell12632)

noncomputable def sourceNumerics12632 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12632 (cell12632 i)
      scalarRow12632.M scalarRow12632.H scalarRow12632.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := pilot_source_cell hi
  have E := pilot_upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := centreCertificate_from_moment (by norm_num)
      (G.window.2.trans (by norm_num)) (pilot_groupMomentCertificate hg)
      hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
    energy_allowance := scalarRow12632.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12632]
    centre_nonneg := (scalarRow12632.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12632])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12632
/-! Actual 12633 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12633
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12633 ≤ (1.035904890103 : ℝ) := by
  have hr : (112.396619166236 : ℝ) ≤ √(12633 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.396619166236 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12633 12633 (11 / 1000) ≤
    (0.008504588979 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12633) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.396619166236 : ℝ) ≤ √(12633 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12633)
  have hdiv : K / √(12633 : ℝ) ≤ K / 112.396619166236 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.396619166236 ≤ (0.008504588979 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12633.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12633 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12633 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12633 := gPlus_lower 12633
end BstLean.Part269.N12633

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12633
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035904890102 : ℝ) ≤ wn 12633 := by
  have hn : √(12633 : ℝ) ≤ 112.396619166237 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12633 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.396619166237 ≤ 2 / √(12633 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253240124 : ℝ) ≤ rhoBar 12633 BstLean.Part154.csC ∧
    rhoBar 12633 BstLean.Part154.csC ≤ 0.000253240516 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035904890102 : ℝ) / (1.295212 * 12633) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035904890103 : ℝ) / (1.29521 * 12633) := by gcongr
      _ ≤ (0.000253240516 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12633 BstLean.Part154.csC) ≤ 0.001013026195 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12633 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12633 BstLean.Part154.csC) (piBar (rhoBar 12633 BstLean.Part154.csC)) ≤ 0.000193426863 ∧
    cc1 (rhoBar 12633 BstLean.Part154.csC) (piBar (rhoBar 12633 BstLean.Part154.csC)) ≤ 0.000123078787 ∧
    cc2 (rhoBar 12633 BstLean.Part154.csC) ≤ 0.000071448167 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12633 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12633 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12633 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12633 BstLean.Part154.csC * nuR (rhoBar 12633 BstLean.Part154.csC)) ≤ 0.000506497065 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253240516 : ℝ) * 0.001013026195 := by gcongr
      _ ≤ (0.000506497065 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12633 BstLean.Part154.csC) * nuR (rhoBar 12633 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001013026195 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12633 BstLean.Part154.csC) * rhoBar 12633 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253240516 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253240516 / 2 + 0.399 * 0.001013026195 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193426863 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506497065 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123078787 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253240516 / 1.414213562 := by gcongr
      _ ≤ (0.000071448167 : ℝ) := by norm_num

end BstLean.Part269.N12633

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12633
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12633 BstLean.Part154.csC) (piBar (rhoBar 12633 BstLean.Part154.csC)) ≤ 1.61573E-7 := by
  have hr0 : 0 ≤ rhoBar 12633 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12633 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12633 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12633 BstLean.Part154.csC) (piBar (rhoBar 12633 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12633 BstLean.Part154.csC) (piBar (rhoBar 12633 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12633 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193426863 : ℝ) ^ 2 + 0.000123078787 ^ 2 + 3 * 0.000071448167 ^ 2 +
        2 * 0.797885 * 0.000193426863 * 0.000123078787 + 2 * 0.000193426863 * 0.000071448167 +
        4 * 0.797885 * 0.000123078787 * 0.000071448167 := by gcongr
    _ ≤ (1.61573E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12633 BstLean.Part154.csC Θ ≤ 0.002643724197 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12633 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12633 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12633 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12633 BstLean.Part154.csC) (piBar (rhoBar 12633 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12633 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035904890103 * 1.61573E-7 / (0.000253240124 : ℝ) := by gcongr
    _ ≤ 0.002643724197 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12633 BstLean.Part154.csC Θ ≤ 0.002933624018 + 0.000668025865 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12633 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12633 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12633 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035904890103 : ℝ) * ((2 * Θ * 0.000253240516 +
        (6863 / 10000) * 0.000253240516 * 12633 * 0.001013026195) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002933624018 + 0.000668025865 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12633 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12633 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12633 0.011 Θ ∧ gammaRatio 12633 0.011 Θ ≤ 0.000087057541 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12633 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035904890103 : ℝ) * 0.525 / ((1 - 0.011) * 12633) := by gcongr
      _ ≤ (0.000087057541 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12633 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12633 0.011 Θ) :=
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
    badAllowance 12633 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12633 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12633 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12633 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12633 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12633 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12633 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12633 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12633 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12633 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12633 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035904890103 : ℝ) * 12633 *
        (2.5110E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12633 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003610330489 + 0.003311750062 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12633

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12633
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12633 BstLean.Part154.csC) (piBar (rhoBar 12633 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12633 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12633 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12633 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12633 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12633 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12633 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12633 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12633 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12633 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12633 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12633 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12633 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12633 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12633 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052624817023 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12633) ≤ 0.010625209103 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12633 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035904890103)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010625209103 + 2 * 0.737676 / 12633) := by gcongr
    _ ≤ (0.052624817023 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12633 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12633

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12633
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500522282 : ℝ) ≤ plow 12633 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12633) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052855599272)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387955204) : eMP 12633 0.011 xi bn ≤ 0.001194810973 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12633 : ℝ) * (1 - 0.011))) ≤ 0.000590760285 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001387955204 / (12633 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590760285 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590760285 : ℝ) + 3.141593 * 0.052855599272 / (12633 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001194810973 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052855599272)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387955204) : PiBarMP 12633 12 0.011 xi bn ≤ 0.161682525428 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12633 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037255270822 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.776728347183 : ℝ) ≤ √((12633 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.396619166236 : ℝ) ≤ √(12633 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12633) ≤ 0.123957538636 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037255270822 + 0.052855599272 * 1.772454 / (2 * (111.776728347183 : ℝ))) * (1 + 0.001194810973) +
        8 / (12633 * 112.396619166236) + 0.123957538636 := by gcongr
    _ ≤ (0.161682525428 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052855599272)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387955204) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282528273439) :
    parallelOracle 12633 0.011 xi bn cd ≤ 0.162678599791 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12633 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12633 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500522282 : ℝ) ≤ plow 12633 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.396619166236 : ℝ) ≤ √(12633 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282528273439 : ℝ) / (2 * 0.560500522282 * 112.396619166236)) * 0.161682525428 +
        0.282528273439 ^ 2 / (2 * 0.560500522282 * 112.396619166236) := by gcongr
    _ ≤ (0.162678599791 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052855599272) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387955204)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282528273439) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12633 12633 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500522282 : ℝ) ≤ plow 12633 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.396619166236 : ℝ) ≤ √(12633 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12633 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12633 Θ 1.22 ≤ 0.011798402033 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.396619166236 := by gcongr <;> linarith
      _ ≤ (0.011798402033 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12633 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12633 12633 0.011 ≤ 0.008504588979 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12633 12633 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12633 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12633 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12633 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12633 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162678599791 + 0.011798402033 + (0.008504588979 : ℝ) *
        (1 + 2 * (0.282528273439 + 0.011798402033) / (0.560500522282 * 112.396619166236))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12633]

end BstLean.Part269.N12633

/-! The original eight local profiles supply actual 12633 moment certificates. -/
namespace BstLean.Part269.N12633
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12633 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part253.group_scalar hg
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
      exact (mul_le_mul_of_nonneg_right (hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part253.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : NeededGroup g) :
    0 ≤ momentAllowance 12633 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12633 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052855599272 ∧
    0 ≤ bN 12633 BstLean.Part154.csC (groupTheta g) ∧ bN 12633 BstLean.Part154.csC (groupTheta g) ≤ 0.001387955204 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12633 12633 0.011
      (momentAllowance 12633 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12633 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12633 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12633 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12633 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12633 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229903456416 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12633 0.011
      (momentAllowance 12633 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12633 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12633
/-! The actual computed-centre upper energy formula at 12633. -/
namespace BstLean.Part269.N12633
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12633

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12633
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12633)
open BstLean.Part268 (cell12633)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085688137105
  | 2 => 0.086634578951
  | 3 => 0.087579708264
  | 4 => 0.088525068645
  | 5 => 0.089472522896
  | 6 => 0.090424299887
  | 7 => 0.091383045709
  | 8 => 0.092351879173
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12633 12633 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12633 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12633

/-! Actual upper energy certificates on all 43 source endpoints at 12633. -/
namespace BstLean.Part269.N12633
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12633)
open BstLean.Part268 (cell12633)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12633 (gMinus 12633) (1 - (cell12633 i).lower) ≤ 1 ∧
    energyUpper 12633 (gMinus 12633) (BstLean.Part211.gPlus 12633)
      (finiteEnergy 12633 12633 0.011) (1 - (cell12633 i).lower) ≤
      (cell12633 i).energy := by
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
  | ⟨10,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨10,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨11,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨12,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨13,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨14,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨15,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨16,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨17,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨18,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨19,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨20,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨21,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨22,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨23,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨24,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨25,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨26,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨27,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨28,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨29,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨30,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨31,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨32,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨33,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨34,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨35,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨36,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨37,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨38,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨39,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨40,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨41,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨42,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨43,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨44,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨45,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨46,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨47,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨48,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨49,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨50,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨51,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12633) (by norm_num)
        (q := 1 - (cell12633 ⟨52,by decide⟩).lower)
        (by norm_num [cell12633]) (by norm_num [cell12633])
      exact ⟨E.1,E.2.trans (by norm_num [cell12633])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12633

/-! Source-cell containment and simple scalar guards at 12633. -/
namespace BstLean.Part269.N12633
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12633)
open BstLean.Part268 (cell12633)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12633 ⟨10,by decide⟩).lower ∧ (cell12633 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12633 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12633 ⟨11,by decide⟩).lower ∧ (cell12633 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12633 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12633 ⟨12,by decide⟩).lower ∧ (cell12633 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12633 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12633 ⟨13,by decide⟩).lower ∧ (cell12633 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12633 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12633 ⟨14,by decide⟩).lower ∧ (cell12633 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12633 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12633 ⟨15,by decide⟩).lower ∧ (cell12633 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12633 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12633 ⟨16,by decide⟩).lower ∧ (cell12633 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12633 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12633 ⟨17,by decide⟩).lower ∧ (cell12633 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12633 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12633 ⟨18,by decide⟩).lower ∧ (cell12633 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12633 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12633 ⟨19,by decide⟩).lower ∧ (cell12633 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12633 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12633 ⟨20,by decide⟩).lower ∧ (cell12633 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12633 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12633 ⟨21,by decide⟩).lower ∧ (cell12633 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12633 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12633 ⟨22,by decide⟩).lower ∧ (cell12633 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12633 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12633 ⟨23,by decide⟩).lower ∧ (cell12633 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12633 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12633 ⟨24,by decide⟩).lower ∧ (cell12633 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12633 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12633 ⟨25,by decide⟩).lower ∧ (cell12633 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12633 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12633 ⟨26,by decide⟩).lower ∧ (cell12633 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12633 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12633 ⟨27,by decide⟩).lower ∧ (cell12633 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12633 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12633 ⟨28,by decide⟩).lower ∧ (cell12633 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12633 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12633 ⟨29,by decide⟩).lower ∧ (cell12633 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12633 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12633 ⟨30,by decide⟩).lower ∧ (cell12633 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12633 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12633 ⟨31,by decide⟩).lower ∧ (cell12633 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12633 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12633 ⟨32,by decide⟩).lower ∧ (cell12633 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12633 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12633 ⟨33,by decide⟩).lower ∧ (cell12633 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12633 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12633 ⟨34,by decide⟩).lower ∧ (cell12633 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12633 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12633 ⟨35,by decide⟩).lower ∧ (cell12633 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12633 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12633 ⟨36,by decide⟩).lower ∧ (cell12633 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12633 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12633 ⟨37,by decide⟩).lower ∧ (cell12633 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12633 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12633 ⟨38,by decide⟩).lower ∧ (cell12633 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12633 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12633 ⟨39,by decide⟩).lower ∧ (cell12633 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12633 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12633 ⟨40,by decide⟩).lower ∧ (cell12633 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12633 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12633 ⟨41,by decide⟩).lower ∧ (cell12633 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12633 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12633 ⟨42,by decide⟩).lower ∧ (cell12633 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12633 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12633 ⟨43,by decide⟩).lower ∧ (cell12633 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12633 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12633 ⟨44,by decide⟩).lower ∧ (cell12633 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12633 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12633 ⟨45,by decide⟩).lower ∧ (cell12633 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12633 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12633 ⟨46,by decide⟩).lower ∧ (cell12633 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12633 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12633 ⟨47,by decide⟩).lower ∧ (cell12633 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12633 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12633 ⟨48,by decide⟩).lower ∧ (cell12633 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12633 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12633 ⟨49,by decide⟩).lower ∧ (cell12633 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12633 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12633 ⟨50,by decide⟩).lower ∧ (cell12633 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12633 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12633 ⟨51,by decide⟩).lower ∧ (cell12633 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12633 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12633 ⟨52,by decide⟩).lower ∧ (cell12633 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12633 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12633 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12633 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12633,cell12633,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12633 i).lower ∧
    (cell12633 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12633 i).upper ≤ (0.532 : ℝ) ∧
    (cell12633 i).centre ≤ (0.1 : ℝ) ∧ (cell12633 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12633 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12633 i).centre = pilotGroupCentre (centreGroup i) := by
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
  | ⟨10,h⟩ => exact pilot_sourceCell10
  | ⟨11,h⟩ => exact pilot_sourceCell11
  | ⟨12,h⟩ => exact pilot_sourceCell12
  | ⟨13,h⟩ => exact pilot_sourceCell13
  | ⟨14,h⟩ => exact pilot_sourceCell14
  | ⟨15,h⟩ => exact pilot_sourceCell15
  | ⟨16,h⟩ => exact pilot_sourceCell16
  | ⟨17,h⟩ => exact pilot_sourceCell17
  | ⟨18,h⟩ => exact pilot_sourceCell18
  | ⟨19,h⟩ => exact pilot_sourceCell19
  | ⟨20,h⟩ => exact pilot_sourceCell20
  | ⟨21,h⟩ => exact pilot_sourceCell21
  | ⟨22,h⟩ => exact pilot_sourceCell22
  | ⟨23,h⟩ => exact pilot_sourceCell23
  | ⟨24,h⟩ => exact pilot_sourceCell24
  | ⟨25,h⟩ => exact pilot_sourceCell25
  | ⟨26,h⟩ => exact pilot_sourceCell26
  | ⟨27,h⟩ => exact pilot_sourceCell27
  | ⟨28,h⟩ => exact pilot_sourceCell28
  | ⟨29,h⟩ => exact pilot_sourceCell29
  | ⟨30,h⟩ => exact pilot_sourceCell30
  | ⟨31,h⟩ => exact pilot_sourceCell31
  | ⟨32,h⟩ => exact pilot_sourceCell32
  | ⟨33,h⟩ => exact pilot_sourceCell33
  | ⟨34,h⟩ => exact pilot_sourceCell34
  | ⟨35,h⟩ => exact pilot_sourceCell35
  | ⟨36,h⟩ => exact pilot_sourceCell36
  | ⟨37,h⟩ => exact pilot_sourceCell37
  | ⟨38,h⟩ => exact pilot_sourceCell38
  | ⟨39,h⟩ => exact pilot_sourceCell39
  | ⟨40,h⟩ => exact pilot_sourceCell40
  | ⟨41,h⟩ => exact pilot_sourceCell41
  | ⟨42,h⟩ => exact pilot_sourceCell42
  | ⟨43,h⟩ => exact pilot_sourceCell43
  | ⟨44,h⟩ => exact pilot_sourceCell44
  | ⟨45,h⟩ => exact pilot_sourceCell45
  | ⟨46,h⟩ => exact pilot_sourceCell46
  | ⟨47,h⟩ => exact pilot_sourceCell47
  | ⟨48,h⟩ => exact pilot_sourceCell48
  | ⟨49,h⟩ => exact pilot_sourceCell49
  | ⟨50,h⟩ => exact pilot_sourceCell50
  | ⟨51,h⟩ => exact pilot_sourceCell51
  | ⟨52,h⟩ => exact pilot_sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12633

/-! The local source numeric instances at 12633 have no network premises. -/
namespace BstLean.Part269.N12633
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12633)
open BstLean.Part268 (cell12633)

noncomputable def sourceNumerics12633 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12633 (cell12633 i)
      scalarRow12633.M scalarRow12633.H scalarRow12633.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := pilot_source_cell hi
  have E := pilot_upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := centreCertificate_from_moment (by norm_num)
      (G.window.2.trans (by norm_num)) (pilot_groupMomentCertificate hg)
      hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
    energy_allowance := scalarRow12633.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12633]
    centre_nonneg := (scalarRow12633.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12633])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12633
/-! Actual 12634 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12634
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12634 ≤ (1.035903456581 : ℝ) := by
  have hr : (112.401067610588 : ℝ) ≤ √(12634 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.401067610588 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12634 12634 (11 / 1000) ≤
    (0.008504252394 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12634) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.401067610588 : ℝ) ≤ √(12634 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12634)
  have hdiv : K / √(12634 : ℝ) ≤ K / 112.401067610588 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.401067610588 ≤ (0.008504252394 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12634.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12634 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12634 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12634 := gPlus_lower 12634
end BstLean.Part269.N12634

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12634
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035903456580 : ℝ) ≤ wn 12634 := by
  have hn : √(12634 : ℝ) ≤ 112.401067610589 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12634 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.401067610589 ≤ 2 / √(12634 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253219730 : ℝ) ≤ rhoBar 12634 BstLean.Part154.csC ∧
    rhoBar 12634 BstLean.Part154.csC ≤ 0.000253220122 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035903456580 : ℝ) / (1.295212 * 12634) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035903456581 : ℝ) / (1.29521 * 12634) := by gcongr
      _ ≤ (0.000253220122 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12634 BstLean.Part154.csC) ≤ 0.001012944609 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12634 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12634 BstLean.Part154.csC) (piBar (rhoBar 12634 BstLean.Part154.csC)) ≤ 0.000193411285 ∧
    cc1 (rhoBar 12634 BstLean.Part154.csC) (piBar (rhoBar 12634 BstLean.Part154.csC)) ≤ 0.000123068875 ∧
    cc2 (rhoBar 12634 BstLean.Part154.csC) ≤ 0.000071442413 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12634 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12634 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12634 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12634 BstLean.Part154.csC * nuR (rhoBar 12634 BstLean.Part154.csC)) ≤ 0.000506456274 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253220122 : ℝ) * 0.001012944609 := by gcongr
      _ ≤ (0.000506456274 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12634 BstLean.Part154.csC) * nuR (rhoBar 12634 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001012944609 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12634 BstLean.Part154.csC) * rhoBar 12634 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253220122 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253220122 / 2 + 0.399 * 0.001012944609 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193411285 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506456274 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123068875 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253220122 / 1.414213562 := by gcongr
      _ ≤ (0.000071442413 : ℝ) := by norm_num

end BstLean.Part269.N12634

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12634
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12634 BstLean.Part154.csC) (piBar (rhoBar 12634 BstLean.Part154.csC)) ≤ 1.61547E-7 := by
  have hr0 : 0 ≤ rhoBar 12634 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12634 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12634 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12634 BstLean.Part154.csC) (piBar (rhoBar 12634 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12634 BstLean.Part154.csC) (piBar (rhoBar 12634 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12634 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193411285 : ℝ) ^ 2 + 0.000123068875 ^ 2 + 3 * 0.000071442413 ^ 2 +
        2 * 0.797885 * 0.000193411285 * 0.000123068875 + 2 * 0.000193411285 * 0.000071442413 +
        4 * 0.797885 * 0.000123068875 * 0.000071442413 := by gcongr
    _ ≤ (1.61547E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12634 BstLean.Part154.csC Θ ≤ 0.002643508004 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12634 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12634 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12634 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12634 BstLean.Part154.csC) (piBar (rhoBar 12634 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12634 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035903456581 * 1.61547E-7 / (0.000253219730 : ℝ) := by gcongr
    _ ≤ 0.002643508004 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12634 BstLean.Part154.csC Θ ≤ 0.002933379644 + 0.000667971143 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12634 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12634 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12634 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035903456581 : ℝ) * ((2 * Θ * 0.000253220122 +
        (6863 / 10000) * 0.000253220122 * 12634 * 0.001012944609) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002933379644 + 0.000667971143 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12634 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12634 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12634 0.011 Θ ∧ gammaRatio 12634 0.011 Θ ≤ 0.000087050530 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12634 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035903456581 : ℝ) * 0.525 / ((1 - 0.011) * 12634) := by gcongr
      _ ≤ (0.000087050530 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12634 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12634 0.011 Θ) :=
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
    badAllowance 12634 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12634 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12634 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12634 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12634 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12634 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12634 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12634 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12634 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12634 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12634 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035903456581 : ℝ) * 12634 *
        (2.5110E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12634 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003610086115 + 0.003311479147 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12634

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12634
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12634 BstLean.Part154.csC) (piBar (rhoBar 12634 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12634 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12634 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12634 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12634 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12634 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12634 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12634 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12634 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12634 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12634 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12634 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12634 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12634 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12634 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052622711672 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12634) ≤ 0.010624788594 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12634 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035903456581)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010624788594 + 2 * 0.737676 / 12634) := by gcongr
    _ ≤ (0.052622711672 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12634 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12634

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12634
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500567983 : ℝ) ≤ plow 12634 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12634) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052855212668)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387841703) : eMP 12634 0.011 xi bn ≤ 0.001194714756 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12634 : ℝ) * (1 - 0.011))) ≤ 0.000590712751 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001387841703 / (12634 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590712751 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590712751 : ℝ) + 3.141593 * 0.052855212668 / (12634 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001194714756 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052855212668)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387841703) : PiBarMP 12634 12 0.011 xi bn ≤ 0.161676070511 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12634 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037253747503 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.781152257435 : ℝ) ≤ √((12634 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.401067610588 : ℝ) ≤ √(12634 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12634) ≤ 0.123952632826 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037253747503 + 0.052855212668 * 1.772454 / (2 * (111.781152257435 : ℝ))) * (1 + 0.001194714756) +
        8 / (12634 * 112.401067610588) + 0.123952632826 := by gcongr
    _ ≤ (0.161676070511 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052855212668)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387841703) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282525327291) :
    parallelOracle 12634 0.011 xi bn cd ≤ 0.162672073906 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12634 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12634 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500567983 : ℝ) ≤ plow 12634 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.401067610588 : ℝ) ≤ √(12634 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282525327291 : ℝ) / (2 * 0.560500567983 * 112.401067610588)) * 0.161676070511 +
        0.282525327291 ^ 2 / (2 * 0.560500567983 * 112.401067610588) := by gcongr
    _ ≤ (0.162672073906 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052855212668) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387841703)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282525327291) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12634 12634 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500567983 : ℝ) ≤ plow 12634 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.401067610588 : ℝ) ≤ √(12634 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12634 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12634 Θ 1.22 ≤ 0.011797935093 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.401067610588 := by gcongr <;> linarith
      _ ≤ (0.011797935093 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12634 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12634 12634 0.011 ≤ 0.008504252394 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12634 12634 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12634 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12634 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12634 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12634 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162672073906 + 0.011797935093 + (0.008504252394 : ℝ) *
        (1 + 2 * (0.282525327291 + 0.011797935093) / (0.560500567983 * 112.401067610588))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12634]

end BstLean.Part269.N12634

/-! The original eight local profiles supply actual 12634 moment certificates. -/
namespace BstLean.Part269.N12634
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12634 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part253.group_scalar hg
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
      exact (mul_le_mul_of_nonneg_right (hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part253.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : NeededGroup g) :
    0 ≤ momentAllowance 12634 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12634 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052855212668 ∧
    0 ≤ bN 12634 BstLean.Part154.csC (groupTheta g) ∧ bN 12634 BstLean.Part154.csC (groupTheta g) ≤ 0.001387841703 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12634 12634 0.011
      (momentAllowance 12634 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12634 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12634 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12634 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12634 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12634 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229902615619 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12634 0.011
      (momentAllowance 12634 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12634 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12634
/-! The actual computed-centre upper energy formula at 12634. -/
namespace BstLean.Part269.N12634
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12634

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12634
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12634)
open BstLean.Part268 (cell12634)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085685146230
  | 2 => 0.086631531407
  | 3 => 0.087576595509
  | 4 => 0.088521880190
  | 5 => 0.089469245964
  | 6 => 0.090420919030
  | 7 => 0.091379542385
  | 8 => 0.092348231273
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12634 12634 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12634 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12634

/-! Actual upper energy certificates on all 43 source endpoints at 12634. -/
namespace BstLean.Part269.N12634
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12634)
open BstLean.Part268 (cell12634)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12634 (gMinus 12634) (1 - (cell12634 i).lower) ≤ 1 ∧
    energyUpper 12634 (gMinus 12634) (BstLean.Part211.gPlus 12634)
      (finiteEnergy 12634 12634 0.011) (1 - (cell12634 i).lower) ≤
      (cell12634 i).energy := by
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
  | ⟨10,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨10,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨11,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨12,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨13,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨14,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨15,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨16,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨17,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨18,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨19,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨20,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨21,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨22,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨23,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨24,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨25,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨26,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨27,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨28,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨29,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨30,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨31,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨32,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨33,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨34,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨35,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨36,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨37,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨38,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨39,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨40,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨41,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨42,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨43,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨44,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨45,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨46,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨47,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨48,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨49,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨50,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨51,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12634) (by norm_num)
        (q := 1 - (cell12634 ⟨52,by decide⟩).lower)
        (by norm_num [cell12634]) (by norm_num [cell12634])
      exact ⟨E.1,E.2.trans (by norm_num [cell12634])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12634

/-! Source-cell containment and simple scalar guards at 12634. -/
namespace BstLean.Part269.N12634
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12634)
open BstLean.Part268 (cell12634)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12634 ⟨10,by decide⟩).lower ∧ (cell12634 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12634 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12634 ⟨11,by decide⟩).lower ∧ (cell12634 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12634 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12634 ⟨12,by decide⟩).lower ∧ (cell12634 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12634 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12634 ⟨13,by decide⟩).lower ∧ (cell12634 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12634 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12634 ⟨14,by decide⟩).lower ∧ (cell12634 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12634 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12634 ⟨15,by decide⟩).lower ∧ (cell12634 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12634 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12634 ⟨16,by decide⟩).lower ∧ (cell12634 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12634 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12634 ⟨17,by decide⟩).lower ∧ (cell12634 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12634 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12634 ⟨18,by decide⟩).lower ∧ (cell12634 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12634 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12634 ⟨19,by decide⟩).lower ∧ (cell12634 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12634 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12634 ⟨20,by decide⟩).lower ∧ (cell12634 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12634 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12634 ⟨21,by decide⟩).lower ∧ (cell12634 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12634 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12634 ⟨22,by decide⟩).lower ∧ (cell12634 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12634 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12634 ⟨23,by decide⟩).lower ∧ (cell12634 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12634 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12634 ⟨24,by decide⟩).lower ∧ (cell12634 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12634 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12634 ⟨25,by decide⟩).lower ∧ (cell12634 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12634 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12634 ⟨26,by decide⟩).lower ∧ (cell12634 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12634 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12634 ⟨27,by decide⟩).lower ∧ (cell12634 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12634 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12634 ⟨28,by decide⟩).lower ∧ (cell12634 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12634 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12634 ⟨29,by decide⟩).lower ∧ (cell12634 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12634 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12634 ⟨30,by decide⟩).lower ∧ (cell12634 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12634 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12634 ⟨31,by decide⟩).lower ∧ (cell12634 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12634 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12634 ⟨32,by decide⟩).lower ∧ (cell12634 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12634 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12634 ⟨33,by decide⟩).lower ∧ (cell12634 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12634 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12634 ⟨34,by decide⟩).lower ∧ (cell12634 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12634 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12634 ⟨35,by decide⟩).lower ∧ (cell12634 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12634 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12634 ⟨36,by decide⟩).lower ∧ (cell12634 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12634 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12634 ⟨37,by decide⟩).lower ∧ (cell12634 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12634 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12634 ⟨38,by decide⟩).lower ∧ (cell12634 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12634 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12634 ⟨39,by decide⟩).lower ∧ (cell12634 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12634 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12634 ⟨40,by decide⟩).lower ∧ (cell12634 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12634 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12634 ⟨41,by decide⟩).lower ∧ (cell12634 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12634 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12634 ⟨42,by decide⟩).lower ∧ (cell12634 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12634 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12634 ⟨43,by decide⟩).lower ∧ (cell12634 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12634 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12634 ⟨44,by decide⟩).lower ∧ (cell12634 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12634 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12634 ⟨45,by decide⟩).lower ∧ (cell12634 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12634 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12634 ⟨46,by decide⟩).lower ∧ (cell12634 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12634 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12634 ⟨47,by decide⟩).lower ∧ (cell12634 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12634 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12634 ⟨48,by decide⟩).lower ∧ (cell12634 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12634 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12634 ⟨49,by decide⟩).lower ∧ (cell12634 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12634 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12634 ⟨50,by decide⟩).lower ∧ (cell12634 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12634 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12634 ⟨51,by decide⟩).lower ∧ (cell12634 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12634 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12634 ⟨52,by decide⟩).lower ∧ (cell12634 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12634 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12634 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12634 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12634,cell12634,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12634 i).lower ∧
    (cell12634 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12634 i).upper ≤ (0.532 : ℝ) ∧
    (cell12634 i).centre ≤ (0.1 : ℝ) ∧ (cell12634 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12634 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12634 i).centre = pilotGroupCentre (centreGroup i) := by
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
  | ⟨10,h⟩ => exact pilot_sourceCell10
  | ⟨11,h⟩ => exact pilot_sourceCell11
  | ⟨12,h⟩ => exact pilot_sourceCell12
  | ⟨13,h⟩ => exact pilot_sourceCell13
  | ⟨14,h⟩ => exact pilot_sourceCell14
  | ⟨15,h⟩ => exact pilot_sourceCell15
  | ⟨16,h⟩ => exact pilot_sourceCell16
  | ⟨17,h⟩ => exact pilot_sourceCell17
  | ⟨18,h⟩ => exact pilot_sourceCell18
  | ⟨19,h⟩ => exact pilot_sourceCell19
  | ⟨20,h⟩ => exact pilot_sourceCell20
  | ⟨21,h⟩ => exact pilot_sourceCell21
  | ⟨22,h⟩ => exact pilot_sourceCell22
  | ⟨23,h⟩ => exact pilot_sourceCell23
  | ⟨24,h⟩ => exact pilot_sourceCell24
  | ⟨25,h⟩ => exact pilot_sourceCell25
  | ⟨26,h⟩ => exact pilot_sourceCell26
  | ⟨27,h⟩ => exact pilot_sourceCell27
  | ⟨28,h⟩ => exact pilot_sourceCell28
  | ⟨29,h⟩ => exact pilot_sourceCell29
  | ⟨30,h⟩ => exact pilot_sourceCell30
  | ⟨31,h⟩ => exact pilot_sourceCell31
  | ⟨32,h⟩ => exact pilot_sourceCell32
  | ⟨33,h⟩ => exact pilot_sourceCell33
  | ⟨34,h⟩ => exact pilot_sourceCell34
  | ⟨35,h⟩ => exact pilot_sourceCell35
  | ⟨36,h⟩ => exact pilot_sourceCell36
  | ⟨37,h⟩ => exact pilot_sourceCell37
  | ⟨38,h⟩ => exact pilot_sourceCell38
  | ⟨39,h⟩ => exact pilot_sourceCell39
  | ⟨40,h⟩ => exact pilot_sourceCell40
  | ⟨41,h⟩ => exact pilot_sourceCell41
  | ⟨42,h⟩ => exact pilot_sourceCell42
  | ⟨43,h⟩ => exact pilot_sourceCell43
  | ⟨44,h⟩ => exact pilot_sourceCell44
  | ⟨45,h⟩ => exact pilot_sourceCell45
  | ⟨46,h⟩ => exact pilot_sourceCell46
  | ⟨47,h⟩ => exact pilot_sourceCell47
  | ⟨48,h⟩ => exact pilot_sourceCell48
  | ⟨49,h⟩ => exact pilot_sourceCell49
  | ⟨50,h⟩ => exact pilot_sourceCell50
  | ⟨51,h⟩ => exact pilot_sourceCell51
  | ⟨52,h⟩ => exact pilot_sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12634

/-! The local source numeric instances at 12634 have no network premises. -/
namespace BstLean.Part269.N12634
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12634)
open BstLean.Part268 (cell12634)

noncomputable def sourceNumerics12634 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12634 (cell12634 i)
      scalarRow12634.M scalarRow12634.H scalarRow12634.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := pilot_source_cell hi
  have E := pilot_upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := centreCertificate_from_moment (by norm_num)
      (G.window.2.trans (by norm_num)) (pilot_groupMomentCertificate hg)
      hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
    energy_allowance := scalarRow12634.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12634]
    centre_nonneg := (scalarRow12634.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12634])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12634
/-! Actual 12635 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12635
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12635 ≤ (1.035902023231 : ℝ) := by
  have hr : (112.405515878892 : ℝ) ≤ √(12635 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.405515878892 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12635 12635 (11 / 1000) ≤
    (0.008503915849 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12635) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.405515878892 : ℝ) ≤ √(12635 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12635)
  have hdiv : K / √(12635 : ℝ) ≤ K / 112.405515878892 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.405515878892 ≤ (0.008503915849 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12635.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12635 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12635 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12635 := gPlus_lower 12635
end BstLean.Part269.N12635

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12635
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035902023230 : ℝ) ≤ wn 12635 := by
  have hn : √(12635 : ℝ) ≤ 112.405515878893 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12635 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.405515878893 ≤ 2 / √(12635 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253199338 : ℝ) ≤ rhoBar 12635 BstLean.Part154.csC ∧
    rhoBar 12635 BstLean.Part154.csC ≤ 0.000253199730 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035902023230 : ℝ) / (1.295212 * 12635) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035902023231 : ℝ) / (1.29521 * 12635) := by gcongr
      _ ≤ (0.000253199730 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12635 BstLean.Part154.csC) ≤ 0.001012863031 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12635 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12635 BstLean.Part154.csC) (piBar (rhoBar 12635 BstLean.Part154.csC)) ≤ 0.000193395709 ∧
    cc1 (rhoBar 12635 BstLean.Part154.csC) (piBar (rhoBar 12635 BstLean.Part154.csC)) ≤ 0.000123058964 ∧
    cc2 (rhoBar 12635 BstLean.Part154.csC) ≤ 0.000071436660 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12635 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12635 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12635 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12635 BstLean.Part154.csC * nuR (rhoBar 12635 BstLean.Part154.csC)) ≤ 0.000506415488 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253199730 : ℝ) * 0.001012863031 := by gcongr
      _ ≤ (0.000506415488 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12635 BstLean.Part154.csC) * nuR (rhoBar 12635 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001012863031 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12635 BstLean.Part154.csC) * rhoBar 12635 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253199730 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253199730 / 2 + 0.399 * 0.001012863031 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193395709 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506415488 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123058964 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253199730 / 1.414213562 := by gcongr
      _ ≤ (0.000071436660 : ℝ) := by norm_num

end BstLean.Part269.N12635

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12635
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12635 BstLean.Part154.csC) (piBar (rhoBar 12635 BstLean.Part154.csC)) ≤ 1.61521E-7 := by
  have hr0 : 0 ≤ rhoBar 12635 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12635 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12635 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12635 BstLean.Part154.csC) (piBar (rhoBar 12635 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12635 BstLean.Part154.csC) (piBar (rhoBar 12635 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12635 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193395709 : ℝ) ^ 2 + 0.000123058964 ^ 2 + 3 * 0.000071436660 ^ 2 +
        2 * 0.797885 * 0.000193395709 * 0.000123058964 + 2 * 0.000193395709 * 0.000071436660 +
        4 * 0.797885 * 0.000123058964 * 0.000071436660 := by gcongr
    _ ≤ (1.61521E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12635 BstLean.Part154.csC Θ ≤ 0.002643291757 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12635 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12635 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12635 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12635 BstLean.Part154.csC) (piBar (rhoBar 12635 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12635 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035902023231 * 1.61521E-7 / (0.000253199338 : ℝ) := by gcongr
    _ ≤ 0.002643291757 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12635 BstLean.Part154.csC Θ ≤ 0.002933135280 + 0.000667916427 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12635 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12635 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12635 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035902023231 : ℝ) * ((2 * Θ * 0.000253199730 +
        (6863 / 10000) * 0.000253199730 * 12635 * 0.001012863031) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002933135280 + 0.000667916427 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12635 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12635 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12635 0.011 Θ ∧ gammaRatio 12635 0.011 Θ ≤ 0.000087043520 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12635 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035902023231 : ℝ) * 0.525 / ((1 - 0.011) * 12635) := by gcongr
      _ ≤ (0.000087043520 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12635 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12635 0.011 Θ) :=
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
    badAllowance 12635 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12635 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12635 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12635 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12635 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12635 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12635 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12635 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12635 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12635 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12635 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035902023231 : ℝ) * 12635 *
        (2.5110E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12635 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003609841751 + 0.003311208184 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12635

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12635
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12635 BstLean.Part154.csC) (piBar (rhoBar 12635 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12635 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12635 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12635 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12635 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12635 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12635 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12635 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12635 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12635 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12635 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12635 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12635 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12635 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12635 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052620606574 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12635) ≤ 0.010624368135 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12635 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035902023231)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010624368135 + 2 * 0.737676 / 12635) := by gcongr
    _ ≤ (0.052620606574 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12635 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12635

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12635
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500613676 : ℝ) ≤ plow 12635 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12635) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052854826048)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387728173) : eMP 12635 0.011 xi bn ≤ 0.001194618531 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12635 : ℝ) * (1 - 0.011))) ≤ 0.000590665213 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001387728173 / (12635 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590665213 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590665213 : ℝ) + 3.141593 * 0.052854826048 / (12635 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001194618531 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052854826048)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387728173) : PiBarMP 12635 12 0.011 xi bn ≤ 0.161669615729 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12635 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037252223733 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.785575992611 : ℝ) ≤ √((12635 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.405515878892 : ℝ) ≤ √(12635 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12635) ≤ 0.123947727599 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037252223733 + 0.052854826048 * 1.772454 / (2 * (111.785575992611 : ℝ))) * (1 + 0.001194618531) +
        8 / (12635 * 112.405515878892) + 0.123947727599 := by gcongr
    _ ≤ (0.161669615729 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052854826048)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387728173) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282522381357) :
    parallelOracle 12635 0.011 xi bn cd ≤ 0.162665548165 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12635 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12635 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500613676 : ℝ) ≤ plow 12635 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.405515878892 : ℝ) ≤ √(12635 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282522381357 : ℝ) / (2 * 0.560500613676 * 112.405515878892)) * 0.161669615729 +
        0.282522381357 ^ 2 / (2 * 0.560500613676 * 112.405515878892) := by gcongr
    _ ≤ (0.162665548165 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052854826048) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387728173)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282522381357) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12635 12635 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500613676 : ℝ) ≤ plow 12635 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.405515878892 : ℝ) ≤ √(12635 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12635 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12635 Θ 1.22 ≤ 0.011797468209 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.405515878892 := by gcongr <;> linarith
      _ ≤ (0.011797468209 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12635 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12635 12635 0.011 ≤ 0.008503915849 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12635 12635 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12635 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12635 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12635 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12635 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162665548165 + 0.011797468209 + (0.008503915849 : ℝ) *
        (1 + 2 * (0.282522381357 + 0.011797468209) / (0.560500613676 * 112.405515878892))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12635]

end BstLean.Part269.N12635

/-! The original eight local profiles supply actual 12635 moment certificates. -/
namespace BstLean.Part269.N12635
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12635 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part253.group_scalar hg
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
      exact (mul_le_mul_of_nonneg_right (hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part253.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : NeededGroup g) :
    0 ≤ momentAllowance 12635 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12635 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052854826048 ∧
    0 ≤ bN 12635 BstLean.Part154.csC (groupTheta g) ∧ bN 12635 BstLean.Part154.csC (groupTheta g) ≤ 0.001387728173 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12635 12635 0.011
      (momentAllowance 12635 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12635 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12635 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12635 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12635 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12635 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229901774783 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12635 0.011
      (momentAllowance 12635 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12635 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12635
/-! The actual computed-centre upper energy formula at 12635. -/
namespace BstLean.Part269.N12635
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12635

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12635
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12635)
open BstLean.Part268 (cell12635)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085682156514
  | 2 => 0.086628485070
  | 3 => 0.087573484022
  | 4 => 0.088518693076
  | 5 => 0.089465970462
  | 6 => 0.090417539713
  | 7 => 0.091376040734
  | 8 => 0.092344585203
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12635 12635 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12635 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12635

/-! Actual upper energy certificates on all 43 source endpoints at 12635. -/
namespace BstLean.Part269.N12635
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12635)
open BstLean.Part268 (cell12635)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12635 (gMinus 12635) (1 - (cell12635 i).lower) ≤ 1 ∧
    energyUpper 12635 (gMinus 12635) (BstLean.Part211.gPlus 12635)
      (finiteEnergy 12635 12635 0.011) (1 - (cell12635 i).lower) ≤
      (cell12635 i).energy := by
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
  | ⟨10,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨10,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨11,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨12,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨13,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨14,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨15,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨16,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨17,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨18,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨19,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨20,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨21,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨22,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨23,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨24,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨25,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨26,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨27,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨28,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨29,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨30,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨31,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨32,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨33,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨34,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨35,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨36,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨37,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨38,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨39,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨40,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨41,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨42,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨43,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨44,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨45,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨46,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨47,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨48,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨49,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨50,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨51,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12635) (by norm_num)
        (q := 1 - (cell12635 ⟨52,by decide⟩).lower)
        (by norm_num [cell12635]) (by norm_num [cell12635])
      exact ⟨E.1,E.2.trans (by norm_num [cell12635])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12635

/-! Source-cell containment and simple scalar guards at 12635. -/
namespace BstLean.Part269.N12635
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12635)
open BstLean.Part268 (cell12635)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12635 ⟨10,by decide⟩).lower ∧ (cell12635 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12635 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12635 ⟨11,by decide⟩).lower ∧ (cell12635 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12635 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12635 ⟨12,by decide⟩).lower ∧ (cell12635 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12635 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12635 ⟨13,by decide⟩).lower ∧ (cell12635 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12635 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12635 ⟨14,by decide⟩).lower ∧ (cell12635 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12635 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12635 ⟨15,by decide⟩).lower ∧ (cell12635 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12635 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12635 ⟨16,by decide⟩).lower ∧ (cell12635 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12635 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12635 ⟨17,by decide⟩).lower ∧ (cell12635 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12635 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12635 ⟨18,by decide⟩).lower ∧ (cell12635 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12635 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12635 ⟨19,by decide⟩).lower ∧ (cell12635 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12635 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12635 ⟨20,by decide⟩).lower ∧ (cell12635 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12635 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12635 ⟨21,by decide⟩).lower ∧ (cell12635 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12635 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12635 ⟨22,by decide⟩).lower ∧ (cell12635 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12635 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12635 ⟨23,by decide⟩).lower ∧ (cell12635 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12635 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12635 ⟨24,by decide⟩).lower ∧ (cell12635 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12635 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12635 ⟨25,by decide⟩).lower ∧ (cell12635 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12635 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12635 ⟨26,by decide⟩).lower ∧ (cell12635 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12635 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12635 ⟨27,by decide⟩).lower ∧ (cell12635 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12635 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12635 ⟨28,by decide⟩).lower ∧ (cell12635 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12635 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12635 ⟨29,by decide⟩).lower ∧ (cell12635 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12635 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12635 ⟨30,by decide⟩).lower ∧ (cell12635 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12635 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12635 ⟨31,by decide⟩).lower ∧ (cell12635 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12635 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12635 ⟨32,by decide⟩).lower ∧ (cell12635 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12635 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12635 ⟨33,by decide⟩).lower ∧ (cell12635 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12635 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12635 ⟨34,by decide⟩).lower ∧ (cell12635 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12635 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12635 ⟨35,by decide⟩).lower ∧ (cell12635 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12635 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12635 ⟨36,by decide⟩).lower ∧ (cell12635 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12635 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12635 ⟨37,by decide⟩).lower ∧ (cell12635 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12635 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12635 ⟨38,by decide⟩).lower ∧ (cell12635 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12635 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12635 ⟨39,by decide⟩).lower ∧ (cell12635 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12635 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12635 ⟨40,by decide⟩).lower ∧ (cell12635 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12635 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12635 ⟨41,by decide⟩).lower ∧ (cell12635 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12635 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12635 ⟨42,by decide⟩).lower ∧ (cell12635 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12635 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12635 ⟨43,by decide⟩).lower ∧ (cell12635 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12635 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12635 ⟨44,by decide⟩).lower ∧ (cell12635 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12635 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12635 ⟨45,by decide⟩).lower ∧ (cell12635 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12635 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12635 ⟨46,by decide⟩).lower ∧ (cell12635 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12635 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12635 ⟨47,by decide⟩).lower ∧ (cell12635 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12635 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12635 ⟨48,by decide⟩).lower ∧ (cell12635 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12635 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12635 ⟨49,by decide⟩).lower ∧ (cell12635 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12635 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12635 ⟨50,by decide⟩).lower ∧ (cell12635 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12635 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12635 ⟨51,by decide⟩).lower ∧ (cell12635 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12635 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12635 ⟨52,by decide⟩).lower ∧ (cell12635 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12635 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12635 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12635 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12635,cell12635,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12635 i).lower ∧
    (cell12635 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12635 i).upper ≤ (0.532 : ℝ) ∧
    (cell12635 i).centre ≤ (0.1 : ℝ) ∧ (cell12635 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12635 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12635 i).centre = pilotGroupCentre (centreGroup i) := by
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
  | ⟨10,h⟩ => exact pilot_sourceCell10
  | ⟨11,h⟩ => exact pilot_sourceCell11
  | ⟨12,h⟩ => exact pilot_sourceCell12
  | ⟨13,h⟩ => exact pilot_sourceCell13
  | ⟨14,h⟩ => exact pilot_sourceCell14
  | ⟨15,h⟩ => exact pilot_sourceCell15
  | ⟨16,h⟩ => exact pilot_sourceCell16
  | ⟨17,h⟩ => exact pilot_sourceCell17
  | ⟨18,h⟩ => exact pilot_sourceCell18
  | ⟨19,h⟩ => exact pilot_sourceCell19
  | ⟨20,h⟩ => exact pilot_sourceCell20
  | ⟨21,h⟩ => exact pilot_sourceCell21
  | ⟨22,h⟩ => exact pilot_sourceCell22
  | ⟨23,h⟩ => exact pilot_sourceCell23
  | ⟨24,h⟩ => exact pilot_sourceCell24
  | ⟨25,h⟩ => exact pilot_sourceCell25
  | ⟨26,h⟩ => exact pilot_sourceCell26
  | ⟨27,h⟩ => exact pilot_sourceCell27
  | ⟨28,h⟩ => exact pilot_sourceCell28
  | ⟨29,h⟩ => exact pilot_sourceCell29
  | ⟨30,h⟩ => exact pilot_sourceCell30
  | ⟨31,h⟩ => exact pilot_sourceCell31
  | ⟨32,h⟩ => exact pilot_sourceCell32
  | ⟨33,h⟩ => exact pilot_sourceCell33
  | ⟨34,h⟩ => exact pilot_sourceCell34
  | ⟨35,h⟩ => exact pilot_sourceCell35
  | ⟨36,h⟩ => exact pilot_sourceCell36
  | ⟨37,h⟩ => exact pilot_sourceCell37
  | ⟨38,h⟩ => exact pilot_sourceCell38
  | ⟨39,h⟩ => exact pilot_sourceCell39
  | ⟨40,h⟩ => exact pilot_sourceCell40
  | ⟨41,h⟩ => exact pilot_sourceCell41
  | ⟨42,h⟩ => exact pilot_sourceCell42
  | ⟨43,h⟩ => exact pilot_sourceCell43
  | ⟨44,h⟩ => exact pilot_sourceCell44
  | ⟨45,h⟩ => exact pilot_sourceCell45
  | ⟨46,h⟩ => exact pilot_sourceCell46
  | ⟨47,h⟩ => exact pilot_sourceCell47
  | ⟨48,h⟩ => exact pilot_sourceCell48
  | ⟨49,h⟩ => exact pilot_sourceCell49
  | ⟨50,h⟩ => exact pilot_sourceCell50
  | ⟨51,h⟩ => exact pilot_sourceCell51
  | ⟨52,h⟩ => exact pilot_sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12635

/-! The local source numeric instances at 12635 have no network premises. -/
namespace BstLean.Part269.N12635
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12635)
open BstLean.Part268 (cell12635)

noncomputable def sourceNumerics12635 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12635 (cell12635 i)
      scalarRow12635.M scalarRow12635.H scalarRow12635.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := pilot_source_cell hi
  have E := pilot_upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := centreCertificate_from_moment (by norm_num)
      (G.window.2.trans (by norm_num)) (pilot_groupMomentCertificate hg)
      hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
    energy_allowance := scalarRow12635.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12635]
    centre_nonneg := (scalarRow12635.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12635])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12635
/-! Actual 12636 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12636
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12636 ≤ (1.035900590052 : ℝ) := by
  have hr : (112.409963971171 : ℝ) ≤ √(12636 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.409963971171 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12636 12636 (11 / 1000) ≤
    (0.008503579344 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12636) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.409963971171 : ℝ) ≤ √(12636 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12636)
  have hdiv : K / √(12636 : ℝ) ≤ K / 112.409963971171 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.409963971171 ≤ (0.008503579344 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12636.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12636 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12636 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12636 := gPlus_lower 12636
end BstLean.Part269.N12636

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12636
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035900590051 : ℝ) ≤ wn 12636 := by
  have hn : √(12636 : ℝ) ≤ 112.409963971172 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12636 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.409963971172 ≤ 2 / √(12636 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253178950 : ℝ) ≤ rhoBar 12636 BstLean.Part154.csC ∧
    rhoBar 12636 BstLean.Part154.csC ≤ 0.000253179342 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035900590051 : ℝ) / (1.295212 * 12636) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035900590052 : ℝ) / (1.29521 * 12636) := by gcongr
      _ ≤ (0.000253179342 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12636 BstLean.Part154.csC) ≤ 0.001012781468 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12636 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12636 BstLean.Part154.csC) (piBar (rhoBar 12636 BstLean.Part154.csC)) ≤ 0.000193380136 ∧
    cc1 (rhoBar 12636 BstLean.Part154.csC) (piBar (rhoBar 12636 BstLean.Part154.csC)) ≤ 0.000123049055 ∧
    cc2 (rhoBar 12636 BstLean.Part154.csC) ≤ 0.000071430908 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12636 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12636 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12636 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12636 BstLean.Part154.csC * nuR (rhoBar 12636 BstLean.Part154.csC)) ≤ 0.000506374709 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253179342 : ℝ) * 0.001012781468 := by gcongr
      _ ≤ (0.000506374709 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12636 BstLean.Part154.csC) * nuR (rhoBar 12636 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001012781468 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12636 BstLean.Part154.csC) * rhoBar 12636 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253179342 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253179342 / 2 + 0.399 * 0.001012781468 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193380136 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506374709 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123049055 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253179342 / 1.414213562 := by gcongr
      _ ≤ (0.000071430908 : ℝ) := by norm_num

end BstLean.Part269.N12636

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12636
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12636 BstLean.Part154.csC) (piBar (rhoBar 12636 BstLean.Part154.csC)) ≤ 1.61495E-7 := by
  have hr0 : 0 ≤ rhoBar 12636 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12636 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12636 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12636 BstLean.Part154.csC) (piBar (rhoBar 12636 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12636 BstLean.Part154.csC) (piBar (rhoBar 12636 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12636 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193380136 : ℝ) ^ 2 + 0.000123049055 ^ 2 + 3 * 0.000071430908 ^ 2 +
        2 * 0.797885 * 0.000193380136 * 0.000123049055 + 2 * 0.000193380136 * 0.000071430908 +
        4 * 0.797885 * 0.000123049055 * 0.000071430908 := by gcongr
    _ ≤ (1.61495E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12636 BstLean.Part154.csC Θ ≤ 0.002643075435 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12636 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12636 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12636 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12636 BstLean.Part154.csC) (piBar (rhoBar 12636 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12636 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035900590052 * 1.61495E-7 / (0.000253178950 : ℝ) := by gcongr
    _ ≤ 0.002643075435 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12636 BstLean.Part154.csC Θ ≤ 0.002932890970 + 0.000667861721 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12636 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12636 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12636 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035900590052 : ℝ) * ((2 * Θ * 0.000253179342 +
        (6863 / 10000) * 0.000253179342 * 12636 * 0.001012781468) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002932890970 + 0.000667861721 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12636 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12636 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12636 0.011 Θ ∧ gammaRatio 12636 0.011 Θ ≤ 0.000087036511 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12636 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035900590052 : ℝ) * 0.525 / ((1 - 0.011) * 12636) := by gcongr
      _ ≤ (0.000087036511 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12636 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12636 0.011 Θ) :=
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
    badAllowance 12636 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12636 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12636 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12636 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12636 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12636 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12636 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12636 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12636 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12636 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12636 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035900590052 : ℝ) * 12636 *
        (2.5110E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12636 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003609597441 + 0.003310937156 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12636

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12636
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12636 BstLean.Part154.csC) (piBar (rhoBar 12636 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12636 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12636 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12636 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12636 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12636 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12636 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12636 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12636 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12636 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12636 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12636 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12636 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12636 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12636 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052618501729 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12636) ≤ 0.010623947726 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12636 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035900590052)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010623947726 + 2 * 0.737676 / 12636) := by gcongr
    _ ≤ (0.052618501729 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12636 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12636

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12636
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500659362 : ℝ) ≤ plow 12636 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12636) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052854439448)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387614604) : eMP 12636 0.011 xi bn ≤ 0.001194522300 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12636 : ℝ) * (1 - 0.011))) ≤ 0.000590617672 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001387614604 / (12636 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590617672 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590617672 : ℝ) + 3.141593 * 0.052854439448 / (12636 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001194522300 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052854439448)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387614604) : PiBarMP 12636 12 0.011 xi bn ≤ 0.161663160943 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12636 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037250699376 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.789999552732 : ℝ) ≤ √((12636 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.409963971171 : ℝ) ≤ √(12636 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12636) ≤ 0.123942822955 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037250699376 + 0.052854439448 * 1.772454 / (2 * (111.789999552732 : ℝ))) * (1 + 0.001194522300) +
        8 / (12636 * 112.409963971171) + 0.123942822955 := by gcongr
    _ ≤ (0.161663160943 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052854439448)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387614604) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282519435716) :
    parallelOracle 12636 0.011 xi bn cd ≤ 0.162659022429 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12636 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12636 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500659362 : ℝ) ≤ plow 12636 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.409963971171 : ℝ) ≤ √(12636 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282519435716 : ℝ) / (2 * 0.560500659362 * 112.409963971171)) * 0.161663160943 +
        0.282519435716 ^ 2 / (2 * 0.560500659362 * 112.409963971171) := by gcongr
    _ ≤ (0.162659022429 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052854439448) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387614604)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282519435716) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12636 12636 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500659362 : ℝ) ≤ plow 12636 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.409963971171 : ℝ) ≤ √(12636 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12636 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12636 Θ 1.22 ≤ 0.011797001380 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.409963971171 := by gcongr <;> linarith
      _ ≤ (0.011797001380 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12636 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12636 12636 0.011 ≤ 0.008503579344 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12636 12636 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12636 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12636 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12636 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12636 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162659022429 + 0.011797001380 + (0.008503579344 : ℝ) *
        (1 + 2 * (0.282519435716 + 0.011797001380) / (0.560500659362 * 112.409963971171))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12636]

end BstLean.Part269.N12636

/-! The original eight local profiles supply actual 12636 moment certificates. -/
namespace BstLean.Part269.N12636
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12636 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part253.group_scalar hg
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
      exact (mul_le_mul_of_nonneg_right (hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part253.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : NeededGroup g) :
    0 ≤ momentAllowance 12636 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12636 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052854439448 ∧
    0 ≤ bN 12636 BstLean.Part154.csC (groupTheta g) ∧ bN 12636 BstLean.Part154.csC (groupTheta g) ≤ 0.001387614604 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12636 12636 0.011
      (momentAllowance 12636 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12636 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12636 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12636 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12636 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12636 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229900933987 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12636 0.011
      (momentAllowance 12636 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12636 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12636
/-! The actual computed-centre upper energy formula at 12636. -/
namespace BstLean.Part269.N12636
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12636

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12636
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12636)
open BstLean.Part268 (cell12636)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085679167957
  | 2 => 0.086625439941
  | 3 => 0.087570373802
  | 4 => 0.088515507302
  | 5 => 0.089462696391
  | 6 => 0.090414161935
  | 7 => 0.091372540753
  | 8 => 0.092340940962
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12636 12636 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12636 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12636

/-! Actual upper energy certificates on all 43 source endpoints at 12636. -/
namespace BstLean.Part269.N12636
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12636)
open BstLean.Part268 (cell12636)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12636 (gMinus 12636) (1 - (cell12636 i).lower) ≤ 1 ∧
    energyUpper 12636 (gMinus 12636) (BstLean.Part211.gPlus 12636)
      (finiteEnergy 12636 12636 0.011) (1 - (cell12636 i).lower) ≤
      (cell12636 i).energy := by
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
  | ⟨10,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨10,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨11,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨12,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨13,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨14,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨15,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨16,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨17,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨18,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨19,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨20,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨21,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨22,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨23,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨24,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨25,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨26,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨27,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨28,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨29,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨30,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨31,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨32,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨33,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨34,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨35,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨36,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨37,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨38,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨39,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨40,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨41,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨42,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨43,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨44,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨45,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨46,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨47,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨48,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨49,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨50,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨51,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12636) (by norm_num)
        (q := 1 - (cell12636 ⟨52,by decide⟩).lower)
        (by norm_num [cell12636]) (by norm_num [cell12636])
      exact ⟨E.1,E.2.trans (by norm_num [cell12636])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12636

/-! Source-cell containment and simple scalar guards at 12636. -/
namespace BstLean.Part269.N12636
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12636)
open BstLean.Part268 (cell12636)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12636 ⟨10,by decide⟩).lower ∧ (cell12636 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12636 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12636 ⟨11,by decide⟩).lower ∧ (cell12636 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12636 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12636 ⟨12,by decide⟩).lower ∧ (cell12636 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12636 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12636 ⟨13,by decide⟩).lower ∧ (cell12636 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12636 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12636 ⟨14,by decide⟩).lower ∧ (cell12636 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12636 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12636 ⟨15,by decide⟩).lower ∧ (cell12636 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12636 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12636 ⟨16,by decide⟩).lower ∧ (cell12636 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12636 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12636 ⟨17,by decide⟩).lower ∧ (cell12636 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12636 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12636 ⟨18,by decide⟩).lower ∧ (cell12636 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12636 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12636 ⟨19,by decide⟩).lower ∧ (cell12636 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12636 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12636 ⟨20,by decide⟩).lower ∧ (cell12636 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12636 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12636 ⟨21,by decide⟩).lower ∧ (cell12636 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12636 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12636 ⟨22,by decide⟩).lower ∧ (cell12636 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12636 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12636 ⟨23,by decide⟩).lower ∧ (cell12636 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12636 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12636 ⟨24,by decide⟩).lower ∧ (cell12636 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12636 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12636 ⟨25,by decide⟩).lower ∧ (cell12636 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12636 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12636 ⟨26,by decide⟩).lower ∧ (cell12636 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12636 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12636 ⟨27,by decide⟩).lower ∧ (cell12636 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12636 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12636 ⟨28,by decide⟩).lower ∧ (cell12636 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12636 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12636 ⟨29,by decide⟩).lower ∧ (cell12636 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12636 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12636 ⟨30,by decide⟩).lower ∧ (cell12636 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12636 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12636 ⟨31,by decide⟩).lower ∧ (cell12636 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12636 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12636 ⟨32,by decide⟩).lower ∧ (cell12636 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12636 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12636 ⟨33,by decide⟩).lower ∧ (cell12636 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12636 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12636 ⟨34,by decide⟩).lower ∧ (cell12636 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12636 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12636 ⟨35,by decide⟩).lower ∧ (cell12636 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12636 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12636 ⟨36,by decide⟩).lower ∧ (cell12636 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12636 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12636 ⟨37,by decide⟩).lower ∧ (cell12636 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12636 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12636 ⟨38,by decide⟩).lower ∧ (cell12636 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12636 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12636 ⟨39,by decide⟩).lower ∧ (cell12636 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12636 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12636 ⟨40,by decide⟩).lower ∧ (cell12636 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12636 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12636 ⟨41,by decide⟩).lower ∧ (cell12636 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12636 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12636 ⟨42,by decide⟩).lower ∧ (cell12636 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12636 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12636 ⟨43,by decide⟩).lower ∧ (cell12636 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12636 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12636 ⟨44,by decide⟩).lower ∧ (cell12636 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12636 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12636 ⟨45,by decide⟩).lower ∧ (cell12636 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12636 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12636 ⟨46,by decide⟩).lower ∧ (cell12636 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12636 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12636 ⟨47,by decide⟩).lower ∧ (cell12636 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12636 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12636 ⟨48,by decide⟩).lower ∧ (cell12636 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12636 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12636 ⟨49,by decide⟩).lower ∧ (cell12636 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12636 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12636 ⟨50,by decide⟩).lower ∧ (cell12636 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12636 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12636 ⟨51,by decide⟩).lower ∧ (cell12636 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12636 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12636 ⟨52,by decide⟩).lower ∧ (cell12636 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12636 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12636 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12636 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12636,cell12636,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12636 i).lower ∧
    (cell12636 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12636 i).upper ≤ (0.532 : ℝ) ∧
    (cell12636 i).centre ≤ (0.1 : ℝ) ∧ (cell12636 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12636 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12636 i).centre = pilotGroupCentre (centreGroup i) := by
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
  | ⟨10,h⟩ => exact pilot_sourceCell10
  | ⟨11,h⟩ => exact pilot_sourceCell11
  | ⟨12,h⟩ => exact pilot_sourceCell12
  | ⟨13,h⟩ => exact pilot_sourceCell13
  | ⟨14,h⟩ => exact pilot_sourceCell14
  | ⟨15,h⟩ => exact pilot_sourceCell15
  | ⟨16,h⟩ => exact pilot_sourceCell16
  | ⟨17,h⟩ => exact pilot_sourceCell17
  | ⟨18,h⟩ => exact pilot_sourceCell18
  | ⟨19,h⟩ => exact pilot_sourceCell19
  | ⟨20,h⟩ => exact pilot_sourceCell20
  | ⟨21,h⟩ => exact pilot_sourceCell21
  | ⟨22,h⟩ => exact pilot_sourceCell22
  | ⟨23,h⟩ => exact pilot_sourceCell23
  | ⟨24,h⟩ => exact pilot_sourceCell24
  | ⟨25,h⟩ => exact pilot_sourceCell25
  | ⟨26,h⟩ => exact pilot_sourceCell26
  | ⟨27,h⟩ => exact pilot_sourceCell27
  | ⟨28,h⟩ => exact pilot_sourceCell28
  | ⟨29,h⟩ => exact pilot_sourceCell29
  | ⟨30,h⟩ => exact pilot_sourceCell30
  | ⟨31,h⟩ => exact pilot_sourceCell31
  | ⟨32,h⟩ => exact pilot_sourceCell32
  | ⟨33,h⟩ => exact pilot_sourceCell33
  | ⟨34,h⟩ => exact pilot_sourceCell34
  | ⟨35,h⟩ => exact pilot_sourceCell35
  | ⟨36,h⟩ => exact pilot_sourceCell36
  | ⟨37,h⟩ => exact pilot_sourceCell37
  | ⟨38,h⟩ => exact pilot_sourceCell38
  | ⟨39,h⟩ => exact pilot_sourceCell39
  | ⟨40,h⟩ => exact pilot_sourceCell40
  | ⟨41,h⟩ => exact pilot_sourceCell41
  | ⟨42,h⟩ => exact pilot_sourceCell42
  | ⟨43,h⟩ => exact pilot_sourceCell43
  | ⟨44,h⟩ => exact pilot_sourceCell44
  | ⟨45,h⟩ => exact pilot_sourceCell45
  | ⟨46,h⟩ => exact pilot_sourceCell46
  | ⟨47,h⟩ => exact pilot_sourceCell47
  | ⟨48,h⟩ => exact pilot_sourceCell48
  | ⟨49,h⟩ => exact pilot_sourceCell49
  | ⟨50,h⟩ => exact pilot_sourceCell50
  | ⟨51,h⟩ => exact pilot_sourceCell51
  | ⟨52,h⟩ => exact pilot_sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12636

/-! The local source numeric instances at 12636 have no network premises. -/
namespace BstLean.Part269.N12636
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12636)
open BstLean.Part268 (cell12636)

noncomputable def sourceNumerics12636 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12636 (cell12636 i)
      scalarRow12636.M scalarRow12636.H scalarRow12636.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := pilot_source_cell hi
  have E := pilot_upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := centreCertificate_from_moment (by norm_num)
      (G.window.2.trans (by norm_num)) (pilot_groupMomentCertificate hg)
      hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
    energy_allowance := scalarRow12636.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12636]
    centre_nonneg := (scalarRow12636.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12636])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12636
/-! Actual 12637 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12637
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12637 ≤ (1.035899157043 : ℝ) := by
  have hr : (112.414411887444 : ℝ) ≤ √(12637 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.414411887444 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12637 12637 (11 / 1000) ≤
    (0.008503242880 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12637) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.414411887444 : ℝ) ≤ √(12637 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12637)
  have hdiv : K / √(12637 : ℝ) ≤ K / 112.414411887444 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.414411887444 ≤ (0.008503242880 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12637.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12637 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12637 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12637 := gPlus_lower 12637
end BstLean.Part269.N12637

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12637
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035899157042 : ℝ) ≤ wn 12637 := by
  have hn : √(12637 : ℝ) ≤ 112.414411887445 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12637 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.414411887445 ≤ 2 / √(12637 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000253158565 : ℝ) ≤ rhoBar 12637 BstLean.Part154.csC ∧
    rhoBar 12637 BstLean.Part154.csC ≤ 0.000253158957 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035899157042 : ℝ) / (1.295212 * 12637) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035899157043 : ℝ) / (1.29521 * 12637) := by gcongr
      _ ≤ (0.000253158957 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12637 BstLean.Part154.csC) ≤ 0.001012699918 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12637 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12637 BstLean.Part154.csC) (piBar (rhoBar 12637 BstLean.Part154.csC)) ≤ 0.000193364565 ∧
    cc1 (rhoBar 12637 BstLean.Part154.csC) (piBar (rhoBar 12637 BstLean.Part154.csC)) ≤ 0.000123039147 ∧
    cc2 (rhoBar 12637 BstLean.Part154.csC) ≤ 0.000071425156 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12637 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12637 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12637 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12637 BstLean.Part154.csC * nuR (rhoBar 12637 BstLean.Part154.csC)) ≤ 0.000506333937 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000253158957 : ℝ) * 0.001012699918 := by gcongr
      _ ≤ (0.000506333937 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12637 BstLean.Part154.csC) * nuR (rhoBar 12637 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001012699918 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12637 BstLean.Part154.csC) * rhoBar 12637 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000253158957 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000253158957 / 2 + 0.399 * 0.001012699918 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000193364565 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000506333937 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000123039147 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000253158957 / 1.414213562 := by gcongr
      _ ≤ (0.000071425156 : ℝ) := by norm_num

end BstLean.Part269.N12637

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12637
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12637 BstLean.Part154.csC) (piBar (rhoBar 12637 BstLean.Part154.csC)) ≤ 1.61469E-7 := by
  have hr0 : 0 ≤ rhoBar 12637 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12637 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12637 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12637 BstLean.Part154.csC) (piBar (rhoBar 12637 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12637 BstLean.Part154.csC) (piBar (rhoBar 12637 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12637 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000193364565 : ℝ) ^ 2 + 0.000123039147 ^ 2 + 3 * 0.000071425156 ^ 2 +
        2 * 0.797885 * 0.000193364565 * 0.000123039147 + 2 * 0.000193364565 * 0.000071425156 +
        4 * 0.797885 * 0.000123039147 * 0.000071425156 := by gcongr
    _ ≤ (1.61469E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12637 BstLean.Part154.csC Θ ≤ 0.002642859048 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12637 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12637 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12637 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12637 BstLean.Part154.csC) (piBar (rhoBar 12637 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12637 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035899157043 * 1.61469E-7 / (0.000253158565 : ℝ) := by gcongr
    _ ≤ 0.002642859048 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12637 BstLean.Part154.csC Θ ≤ 0.002932646697 + 0.000667807024 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12637 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12637 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12637 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035899157043 : ℝ) * ((2 * Θ * 0.000253158957 +
        (6863 / 10000) * 0.000253158957 * 12637 * 0.001012699918) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002932646697 + 0.000667807024 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12637 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12637 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12637 0.011 Θ ∧ gammaRatio 12637 0.011 Θ ≤ 0.000087029503 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12637 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035899157043 : ℝ) * 0.525 / ((1 - 0.011) * 12637) := by gcongr
      _ ≤ (0.000087029503 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12637 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12637 0.011 Θ) :=
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
    badAllowance 12637 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000676706471 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12637 BstLean.Part154.csC) 1.22 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 2 (rhoBar 12637 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12637 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12637 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12637 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12637 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12637 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12637 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12637 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12637 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035899157043 : ℝ) * 12637 *
        (2.5110E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000676706471 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12637 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003609353168 + 0.003310666072 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12637

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12637
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12637 BstLean.Part154.csC) (piBar (rhoBar 12637 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12637 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12637 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12637 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12637 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12637 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12637 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12637 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12637 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12637 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12637 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12637 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12637 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12637 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12637 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052616397135 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12637) ≤ 0.010623527367 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12637 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035899157043)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010623527367 + 2 * 0.737676 / 12637) := by gcongr
    _ ≤ (0.052616397135 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12637 12 ≤ 0.0015 := by
  exact BstLean.Part269.S11.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12637

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12637
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560500705040 : ℝ) ≤ plow 12637 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12637) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052854052856)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387501001) : eMP 12637 0.011 xi bn ≤ 0.001194426059 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12637 : ℝ) * (1 - 0.011))) ≤ 0.000590570126 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001387501001 / (12637 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000590570126 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000590570126 : ℝ) + 3.141593 * 0.052854052856 / (12637 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001194426059 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052854052856)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387501001) : PiBarMP 12637 12 0.011 xi bn ≤ 0.161656706223 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12637 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037249174501 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.794422937819 : ℝ) ≤ √((12637 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.414411887444 : ℝ) ≤ √(12637 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12637) ≤ 0.123937918892 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037249174501 + 0.052854052856 * 1.772454 / (2 * (111.794422937819 : ℝ))) * (1 + 0.001194426059) +
        8 / (12637 * 112.414411887444) + 0.123937918892 := by gcongr
    _ ≤ (0.161656706223 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052854052856)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387501001) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282516490341) :
    parallelOracle 12637 0.011 xi bn cd ≤ 0.162652496769 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12637 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12637 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560500705040 : ℝ) ≤ plow 12637 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.414411887444 : ℝ) ≤ √(12637 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282516490341 : ℝ) / (2 * 0.560500705040 * 112.414411887444)) * 0.161656706223 +
        0.282516490341 ^ 2 / (2 * 0.560500705040 * 112.414411887444) := by gcongr
    _ ≤ (0.162652496769 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052854052856) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001387501001)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282516490341) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12637 12637 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560500705040 : ℝ) ≤ plow 12637 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.414411887444 : ℝ) ≤ √(12637 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12637 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12637 Θ 1.22 ≤ 0.011796534606 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.414411887444 := by gcongr <;> linarith
      _ ≤ (0.011796534606 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12637 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12637 12637 0.011 ≤ 0.008503242880 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12637 12637 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12637 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12637 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12637 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12637 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162652496769 + 0.011796534606 + (0.008503242880 : ℝ) *
        (1 + 2 * (0.282516490341 + 0.011796534606) / (0.560500705040 * 112.414411887444))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12637]

end BstLean.Part269.N12637

/-! The original eight local profiles supply actual 12637 moment certificates. -/
namespace BstLean.Part269.N12637
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12637 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
      (fun _ => 0.006) := by
  have G := BstLean.Part253.group_scalar hg
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
      exact (mul_le_mul_of_nonneg_right (hsProfile_le (by norm_num) hθ0 hθ1)
        (by positivity : 0 ≤ θ * √θ)).trans (BstLean.Part253.profile_on_group hg hθ)
    ratio := by have := pilot_rho_bounds.2; linarith
    ratio_gamma := by have := (pilot_gamma_bounds G.window).2; linarith
    gap := lt_of_lt_of_le (by norm_num) pilot_first_gap_lower
    gap_gamma := lt_of_lt_of_le (by norm_num) (pilot_second_gap_lower G.window) }

theorem pilot_group_moment_bounds {g : Fin 10} (hg : NeededGroup g) :
    0 ≤ momentAllowance 12637 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12637 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052854052856 ∧
    0 ≤ bN 12637 BstLean.Part154.csC (groupTheta g) ∧ bN 12637 BstLean.Part154.csC (groupTheta g) ≤ 0.001387501001 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12637 12637 0.011
      (momentAllowance 12637 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12637 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12637 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12637 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12637 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12637 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229900093206 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12637 0.011
      (momentAllowance 12637 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12637 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12637
/-! The actual computed-centre upper energy formula at 12637. -/
namespace BstLean.Part269.N12637
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12637

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12637
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12637)
open BstLean.Part268 (cell12637)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085676180556
  | 2 => 0.086622396017
  | 3 => 0.087567264847
  | 4 => 0.088512322867
  | 5 => 0.089459423747
  | 6 => 0.090410785695
  | 7 => 0.091369042440
  | 8 => 0.092337298548
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12637 12637 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12637 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003612287085 + 0.003313915228 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S11.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S11.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12637

/-! Actual upper energy certificates on all 43 source endpoints at 12637. -/
namespace BstLean.Part269.N12637
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12637)
open BstLean.Part268 (cell12637)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12637 (gMinus 12637) (1 - (cell12637 i).lower) ≤ 1 ∧
    energyUpper 12637 (gMinus 12637) (BstLean.Part211.gPlus 12637)
      (finiteEnergy 12637 12637 0.011) (1 - (cell12637 i).lower) ≤
      (cell12637 i).energy := by
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
  | ⟨10,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy10 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨10,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy11 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨11,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy12 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨12,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy13 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨13,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy14 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨14,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy15 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨15,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy16 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨16,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy17 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨17,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy18 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨18,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy19 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨19,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy20 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨20,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy21 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨21,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy22 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨22,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy23 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨23,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy24 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨24,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy25 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨25,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy26 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨26,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy27 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨27,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy28 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨28,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy29 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨29,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy30 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨30,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy31 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨31,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy32 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨32,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy33 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨33,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy34 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨34,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy35 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨35,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy36 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨36,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy37 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨37,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy38 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨38,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy39 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨39,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy40 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨40,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy41 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨41,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy42 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨42,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy43 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨43,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy44 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨44,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy45 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨45,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy46 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨46,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy47 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨47,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy48 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨48,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy49 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨49,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy50 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨50,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy51 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨51,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S11.uniformEnergy52 (n := 12637) (by norm_num)
        (q := 1 - (cell12637 ⟨52,by decide⟩).lower)
        (by norm_num [cell12637]) (by norm_num [cell12637])
      exact ⟨E.1,E.2.trans (by norm_num [cell12637])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12637

/-! Source-cell containment and simple scalar guards at 12637. -/
namespace BstLean.Part269.N12637
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12637)
open BstLean.Part268 (cell12637)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12637 ⟨10,by decide⟩).lower ∧ (cell12637 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12637 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12637 ⟨11,by decide⟩).lower ∧ (cell12637 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12637 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12637 ⟨12,by decide⟩).lower ∧ (cell12637 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12637 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12637 ⟨13,by decide⟩).lower ∧ (cell12637 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12637 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12637 ⟨14,by decide⟩).lower ∧ (cell12637 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12637 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12637 ⟨15,by decide⟩).lower ∧ (cell12637 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12637 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12637 ⟨16,by decide⟩).lower ∧ (cell12637 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12637 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12637 ⟨17,by decide⟩).lower ∧ (cell12637 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12637 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12637 ⟨18,by decide⟩).lower ∧ (cell12637 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12637 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12637 ⟨19,by decide⟩).lower ∧ (cell12637 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12637 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12637 ⟨20,by decide⟩).lower ∧ (cell12637 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12637 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12637 ⟨21,by decide⟩).lower ∧ (cell12637 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12637 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12637 ⟨22,by decide⟩).lower ∧ (cell12637 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12637 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12637 ⟨23,by decide⟩).lower ∧ (cell12637 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12637 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12637 ⟨24,by decide⟩).lower ∧ (cell12637 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12637 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12637 ⟨25,by decide⟩).lower ∧ (cell12637 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12637 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12637 ⟨26,by decide⟩).lower ∧ (cell12637 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12637 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12637 ⟨27,by decide⟩).lower ∧ (cell12637 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12637 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12637 ⟨28,by decide⟩).lower ∧ (cell12637 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12637 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12637 ⟨29,by decide⟩).lower ∧ (cell12637 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12637 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12637 ⟨30,by decide⟩).lower ∧ (cell12637 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12637 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12637 ⟨31,by decide⟩).lower ∧ (cell12637 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12637 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12637 ⟨32,by decide⟩).lower ∧ (cell12637 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12637 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12637 ⟨33,by decide⟩).lower ∧ (cell12637 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12637 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12637 ⟨34,by decide⟩).lower ∧ (cell12637 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12637 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12637 ⟨35,by decide⟩).lower ∧ (cell12637 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12637 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12637 ⟨36,by decide⟩).lower ∧ (cell12637 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12637 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12637 ⟨37,by decide⟩).lower ∧ (cell12637 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12637 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12637 ⟨38,by decide⟩).lower ∧ (cell12637 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12637 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12637 ⟨39,by decide⟩).lower ∧ (cell12637 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12637 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12637 ⟨40,by decide⟩).lower ∧ (cell12637 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12637 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12637 ⟨41,by decide⟩).lower ∧ (cell12637 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12637 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12637 ⟨42,by decide⟩).lower ∧ (cell12637 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12637 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12637 ⟨43,by decide⟩).lower ∧ (cell12637 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12637 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12637 ⟨44,by decide⟩).lower ∧ (cell12637 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12637 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12637 ⟨45,by decide⟩).lower ∧ (cell12637 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12637 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12637 ⟨46,by decide⟩).lower ∧ (cell12637 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12637 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12637 ⟨47,by decide⟩).lower ∧ (cell12637 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12637 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12637 ⟨48,by decide⟩).lower ∧ (cell12637 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12637 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12637 ⟨49,by decide⟩).lower ∧ (cell12637 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12637 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12637 ⟨50,by decide⟩).lower ∧ (cell12637 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12637 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12637 ⟨51,by decide⟩).lower ∧ (cell12637 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12637 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12637 ⟨52,by decide⟩).lower ∧ (cell12637 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12637 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12637 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12637 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12637,cell12637,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12637 i).lower ∧
    (cell12637 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12637 i).upper ≤ (0.532 : ℝ) ∧
    (cell12637 i).centre ≤ (0.1 : ℝ) ∧ (cell12637 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12637 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12637 i).centre = pilotGroupCentre (centreGroup i) := by
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
  | ⟨10,h⟩ => exact pilot_sourceCell10
  | ⟨11,h⟩ => exact pilot_sourceCell11
  | ⟨12,h⟩ => exact pilot_sourceCell12
  | ⟨13,h⟩ => exact pilot_sourceCell13
  | ⟨14,h⟩ => exact pilot_sourceCell14
  | ⟨15,h⟩ => exact pilot_sourceCell15
  | ⟨16,h⟩ => exact pilot_sourceCell16
  | ⟨17,h⟩ => exact pilot_sourceCell17
  | ⟨18,h⟩ => exact pilot_sourceCell18
  | ⟨19,h⟩ => exact pilot_sourceCell19
  | ⟨20,h⟩ => exact pilot_sourceCell20
  | ⟨21,h⟩ => exact pilot_sourceCell21
  | ⟨22,h⟩ => exact pilot_sourceCell22
  | ⟨23,h⟩ => exact pilot_sourceCell23
  | ⟨24,h⟩ => exact pilot_sourceCell24
  | ⟨25,h⟩ => exact pilot_sourceCell25
  | ⟨26,h⟩ => exact pilot_sourceCell26
  | ⟨27,h⟩ => exact pilot_sourceCell27
  | ⟨28,h⟩ => exact pilot_sourceCell28
  | ⟨29,h⟩ => exact pilot_sourceCell29
  | ⟨30,h⟩ => exact pilot_sourceCell30
  | ⟨31,h⟩ => exact pilot_sourceCell31
  | ⟨32,h⟩ => exact pilot_sourceCell32
  | ⟨33,h⟩ => exact pilot_sourceCell33
  | ⟨34,h⟩ => exact pilot_sourceCell34
  | ⟨35,h⟩ => exact pilot_sourceCell35
  | ⟨36,h⟩ => exact pilot_sourceCell36
  | ⟨37,h⟩ => exact pilot_sourceCell37
  | ⟨38,h⟩ => exact pilot_sourceCell38
  | ⟨39,h⟩ => exact pilot_sourceCell39
  | ⟨40,h⟩ => exact pilot_sourceCell40
  | ⟨41,h⟩ => exact pilot_sourceCell41
  | ⟨42,h⟩ => exact pilot_sourceCell42
  | ⟨43,h⟩ => exact pilot_sourceCell43
  | ⟨44,h⟩ => exact pilot_sourceCell44
  | ⟨45,h⟩ => exact pilot_sourceCell45
  | ⟨46,h⟩ => exact pilot_sourceCell46
  | ⟨47,h⟩ => exact pilot_sourceCell47
  | ⟨48,h⟩ => exact pilot_sourceCell48
  | ⟨49,h⟩ => exact pilot_sourceCell49
  | ⟨50,h⟩ => exact pilot_sourceCell50
  | ⟨51,h⟩ => exact pilot_sourceCell51
  | ⟨52,h⟩ => exact pilot_sourceCell52
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12637

/-! The local source numeric instances at 12637 have no network premises. -/
namespace BstLean.Part269.N12637
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12637)
open BstLean.Part268 (cell12637)

noncomputable def sourceNumerics12637 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12637 (cell12637 i)
      scalarRow12637.M scalarRow12637.H scalarRow12637.xi := by
  have hg : NeededGroup (centreGroup i) := BstLean.Part253.needed_group hi
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hl,hu,hu532,hc,hE,hq,hcentre⟩ := pilot_source_cell hi
  have E := pilot_upper_energy hi
  exact {
    thetaHi := groupTheta (centreGroup i)
    S := groupProfile (centreGroup i)
    certificate := centreCertificate_from_moment (by norm_num)
      (G.window.2.trans (by norm_num)) (pilot_groupMomentCertificate hg)
      hq E.1 (pilot_group_relative_gap hg) (E.2.trans hE)
    energy_allowance := scalarRow12637.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12637]
    centre_nonneg := (scalarRow12637.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D11.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12637])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12637