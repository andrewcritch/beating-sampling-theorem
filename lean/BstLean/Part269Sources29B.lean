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
import BstLean.Part269Direction29
import BstLean.Part269Shared29
import BstLean.Part269Finite
import BstLean.Part269Rows29
import BstLean.Part269Source
/-! Actual 13088 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13088
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13088 ≤ (1.035269803536 : ℝ) := by
  have hr : (114.402797168600 : ℝ) ≤ √(13088 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.402797168600 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13088 13088 (11 / 1000) ≤
    (0.008355450599 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13088) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.402797168600 : ℝ) ≤ √(13088 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13088)
  have hdiv : K / √(13088 : ℝ) ≤ K / 114.402797168600 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.402797168600 ≤ (0.008355450599 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13088.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13088 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13088 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13088 := gPlus_lower 13088
end BstLean.Part269.N13088

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13088
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035269803535 : ℝ) ≤ wn 13088 := by
  have hn : √(13088 : ℝ) ≤ 114.402797168601 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13088 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.402797168601 ≤ 2 / √(13088 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244286457 : ℝ) ≤ rhoBar 13088 BstLean.Part154.csC ∧
    rhoBar 13088 BstLean.Part154.csC ≤ 0.000244286836 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035269803535 : ℝ) / (1.295212 * 13088) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035269803536 : ℝ) / (1.29521 * 13088) := by gcongr
      _ ≤ (0.000244286836 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13088 BstLean.Part154.csC) ≤ 0.000977207021 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13088 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13088 BstLean.Part154.csC) (piBar (rhoBar 13088 BstLean.Part154.csC)) ≤ 0.000186587672 ∧
    cc1 (rhoBar 13088 BstLean.Part154.csC) (piBar (rhoBar 13088 BstLean.Part154.csC)) ≤ 0.000118727028 ∧
    cc2 (rhoBar 13088 BstLean.Part154.csC) ≤ 0.000068922015 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13088 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13088 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13088 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13088 BstLean.Part154.csC * nuR (rhoBar 13088 BstLean.Part154.csC)) ≤ 0.000488588592 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244286836 : ℝ) * 0.000977207021 := by gcongr
      _ ≤ (0.000488588592 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13088 BstLean.Part154.csC) * nuR (rhoBar 13088 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000977207021 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13088 BstLean.Part154.csC) * rhoBar 13088 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244286836 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244286836 / 2 + 0.399 * 0.000977207021 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186587672 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488588592 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118727028 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244286836 / 1.414213562 := by gcongr
      _ ≤ (0.000068922015 : ℝ) := by norm_num

end BstLean.Part269.N13088

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13088
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13088 BstLean.Part154.csC) (piBar (rhoBar 13088 BstLean.Part154.csC)) ≤ 1.50349E-7 := by
  have hr0 : 0 ≤ rhoBar 13088 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13088 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13088 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13088 BstLean.Part154.csC) (piBar (rhoBar 13088 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13088 BstLean.Part154.csC) (piBar (rhoBar 13088 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13088 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186587672 : ℝ) ^ 2 + 0.000118727028 ^ 2 + 3 * 0.000068922015 ^ 2 +
        2 * 0.797885 * 0.000186587672 * 0.000118727028 + 2 * 0.000186587672 * 0.000068922015 +
        4 * 0.797885 * 0.000118727028 * 0.000068922015 := by gcongr
    _ ≤ (1.50349E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13088 BstLean.Part154.csC Θ ≤ 0.002548676364 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13088 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13088 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13088 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13088 BstLean.Part154.csC) (piBar (rhoBar 13088 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13088 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035269803536 * 1.50349E-7 / (0.000244286457 : ℝ) := by gcongr
    _ ≤ 0.002548676364 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13088 BstLean.Part154.csC Θ ≤ 0.002826426422 + 0.000644011787 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13088 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13088 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13088 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035269803536 : ℝ) * ((2 * Θ * 0.000244286836 +
        (6863 / 10000) * 0.000244286836 * 13088 * 0.000977207021) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002826426422 + 0.000644011787 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13088 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13088 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13088 0.011 Θ ∧ gammaRatio 13088 0.011 Θ ≤ 0.000083979497 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13088 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035269803536 : ℝ) * 0.525 / ((1 - 0.011) * 13088) := by gcongr
      _ ≤ (0.000083979497 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13088 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13088 0.011 Θ) :=
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
    badAllowance 13088 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13088 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13088 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13088 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13088 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13088 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13088 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13088 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13088 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13088 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13088 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035269803536 : ℝ) * 13088 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13088 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003174678770 + 0.003192688151 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13088

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13088
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13088 BstLean.Part154.csC) (piBar (rhoBar 13088 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13088 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13088 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13088 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13088 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13088 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13088 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13088 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13088 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13088 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13088 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13088 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13088 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13088 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13088 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051692126388 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13088) ≤ 0.010438884456 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13088 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035269803536)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010438884456 + 2 * 0.737676 / 13088) := by gcongr
    _ ≤ (0.051692126388 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13088 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13088

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13088
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520594628 : ℝ) ≤ plow 13088 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13088) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052357440050)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338055092) : eMP 13088 0.011 xi bn ≤ 0.001152451068 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13088 : ℝ) * (1 - 0.011))) ≤ 0.000569871804 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001338055092 / (13088 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569871804 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569871804 : ℝ) + 3.141593 * 0.052357440050 / (13088 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001152451068 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052357440050)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338055092) : PiBarMP 13088 12 0.011 xi bn ≤ 0.158819050987 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13088 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036579435371 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.771841859047 : ℝ) ≤ √((13088 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.402797168600 : ℝ) ≤ √(13088 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13088) ≤ 0.121783807806 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036579435371 + 0.052357440050 * 1.772454 / (2 * (113.771841859047 : ℝ))) * (1 + 0.001152451068) +
        8 / (13088 * 114.402797168600) + 0.121783807806 := by gcongr
    _ ≤ (0.158819050987 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052357440050)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338055092) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280509608347) :
    parallelOracle 13088 0.011 xi bn cd ≤ 0.159779952914 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13088 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13088 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520594628 : ℝ) ≤ plow 13088 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.402797168600 : ℝ) ≤ √(13088 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280509608347 : ℝ) / (2 * 0.560520594628 * 114.402797168600)) * 0.158819050987 +
        0.280509608347 ^ 2 / (2 * 0.560520594628 * 114.402797168600) := by gcongr
    _ ≤ (0.159779952914 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052357440050) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338055092)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280509608347) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13088 13088 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520594628 : ℝ) ≤ plow 13088 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.402797168600 : ℝ) ≤ √(13088 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13088 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13088 Θ 1.22 ≤ 0.011591504167 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.402797168600 := by gcongr <;> linarith
      _ ≤ (0.011591504167 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13088 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13088 13088 0.011 ≤ 0.008355450599 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13088 13088 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13088 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13088 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13088 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13088 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159779952914 + 0.011591504167 + (0.008355450599 : ℝ) *
        (1 + 2 * (0.280509608347 + 0.011591504167) / (0.560520594628 * 114.402797168600))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13088]

end BstLean.Part269.N13088

/-! The original eight local profiles supply actual 13088 moment certificates. -/
namespace BstLean.Part269.N13088
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13088 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13088 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13088 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052357440050 ∧
    0 ≤ bN 13088 BstLean.Part154.csC (groupTheta g) ∧ bN 13088 BstLean.Part154.csC (groupTheta g) ≤ 0.001338055092 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13088 13088 0.011
      (momentAllowance 13088 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13088 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13088 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13088 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13088 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13088 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228817481959 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13088 0.011
      (momentAllowance 13088 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13088 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13088
/-! The actual computed-centre upper energy formula at 13088. -/
namespace BstLean.Part269.N13088
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13088

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13088
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13088)
open BstLean.Part268 (cell13088)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084432721189
  | 2 => 0.085358459502
  | 3 => 0.086279969650
  | 4 => 0.087198112978
  | 5 => 0.088113947341
  | 6 => 0.089028758264
  | 7 => 0.089944093394
  | 8 => 0.090861800378
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13088 13088 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13088 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003177634099 + 0.003195984085 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S29.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13088

/-! Actual upper energy certificates on all 43 source endpoints at 13088. -/
namespace BstLean.Part269.N13088
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13088)
open BstLean.Part268 (cell13088)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13088 (gMinus 13088) (1 - (cell13088 i).lower) ≤ 1 ∧
    energyUpper 13088 (gMinus 13088) (BstLean.Part211.gPlus 13088)
      (finiteEnergy 13088 13088 0.011) (1 - (cell13088 i).lower) ≤
      (cell13088 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨10,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨11,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨12,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨13,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨14,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨15,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨16,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨17,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨18,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨19,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨20,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨21,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨22,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨23,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨24,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨25,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨26,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨27,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨28,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨29,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨30,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨31,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨32,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨33,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨34,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨35,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨36,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨37,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨38,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨39,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨40,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨41,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨42,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨43,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨44,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨45,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨46,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨47,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨48,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨49,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨50,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨51,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13088) (by norm_num)
        (q := 1 - (cell13088 ⟨52,by decide⟩).lower)
        (by norm_num [cell13088]) (by norm_num [cell13088])
      exact ⟨E.1,E.2.trans (by norm_num [cell13088])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13088

/-! Source-cell containment and simple scalar guards at 13088. -/
namespace BstLean.Part269.N13088
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13088)
open BstLean.Part268 (cell13088)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13088 ⟨10,by decide⟩).lower ∧ (cell13088 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13088 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13088 ⟨11,by decide⟩).lower ∧ (cell13088 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13088 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13088 ⟨12,by decide⟩).lower ∧ (cell13088 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13088 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13088 ⟨13,by decide⟩).lower ∧ (cell13088 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13088 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13088 ⟨14,by decide⟩).lower ∧ (cell13088 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13088 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13088 ⟨15,by decide⟩).lower ∧ (cell13088 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13088 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13088 ⟨16,by decide⟩).lower ∧ (cell13088 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13088 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13088 ⟨17,by decide⟩).lower ∧ (cell13088 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13088 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13088 ⟨18,by decide⟩).lower ∧ (cell13088 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13088 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13088 ⟨19,by decide⟩).lower ∧ (cell13088 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13088 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13088 ⟨20,by decide⟩).lower ∧ (cell13088 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13088 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13088 ⟨21,by decide⟩).lower ∧ (cell13088 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13088 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13088 ⟨22,by decide⟩).lower ∧ (cell13088 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13088 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13088 ⟨23,by decide⟩).lower ∧ (cell13088 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13088 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13088 ⟨24,by decide⟩).lower ∧ (cell13088 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13088 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13088 ⟨25,by decide⟩).lower ∧ (cell13088 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13088 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13088 ⟨26,by decide⟩).lower ∧ (cell13088 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13088 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13088 ⟨27,by decide⟩).lower ∧ (cell13088 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13088 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13088 ⟨28,by decide⟩).lower ∧ (cell13088 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13088 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13088 ⟨29,by decide⟩).lower ∧ (cell13088 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13088 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13088 ⟨30,by decide⟩).lower ∧ (cell13088 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13088 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13088 ⟨31,by decide⟩).lower ∧ (cell13088 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13088 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13088 ⟨32,by decide⟩).lower ∧ (cell13088 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13088 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13088 ⟨33,by decide⟩).lower ∧ (cell13088 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13088 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13088 ⟨34,by decide⟩).lower ∧ (cell13088 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13088 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13088 ⟨35,by decide⟩).lower ∧ (cell13088 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13088 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13088 ⟨36,by decide⟩).lower ∧ (cell13088 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13088 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13088 ⟨37,by decide⟩).lower ∧ (cell13088 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13088 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13088 ⟨38,by decide⟩).lower ∧ (cell13088 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13088 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13088 ⟨39,by decide⟩).lower ∧ (cell13088 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13088 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13088 ⟨40,by decide⟩).lower ∧ (cell13088 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13088 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13088 ⟨41,by decide⟩).lower ∧ (cell13088 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13088 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13088 ⟨42,by decide⟩).lower ∧ (cell13088 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13088 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13088 ⟨43,by decide⟩).lower ∧ (cell13088 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13088 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13088 ⟨44,by decide⟩).lower ∧ (cell13088 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13088 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13088 ⟨45,by decide⟩).lower ∧ (cell13088 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13088 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13088 ⟨46,by decide⟩).lower ∧ (cell13088 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13088 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13088 ⟨47,by decide⟩).lower ∧ (cell13088 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13088 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13088 ⟨48,by decide⟩).lower ∧ (cell13088 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13088 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13088 ⟨49,by decide⟩).lower ∧ (cell13088 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13088 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13088 ⟨50,by decide⟩).lower ∧ (cell13088 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13088 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13088 ⟨51,by decide⟩).lower ∧ (cell13088 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13088 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13088 ⟨52,by decide⟩).lower ∧ (cell13088 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13088 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13088 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13088 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13088,cell13088,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13088 i).lower ∧
    (cell13088 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13088 i).upper ≤ (0.532 : ℝ) ∧
    (cell13088 i).centre ≤ (0.1 : ℝ) ∧ (cell13088 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13088 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13088 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13088

/-! The local source numeric instances at 13088 have no network premises. -/
namespace BstLean.Part269.N13088
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13088)
open BstLean.Part268 (cell13088)

noncomputable def sourceNumerics13088 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13088 (cell13088 i)
      scalarRow13088.M scalarRow13088.H scalarRow13088.xi := by
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
    energy_allowance := scalarRow13088.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13088]
    centre_nonneg := (scalarRow13088.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13088])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13088
/-! Actual 13089 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13089
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13089 ≤ (1.035268444529 : ℝ) := by
  have hr : (114.407167607628 : ℝ) ≤ √(13089 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.407167607628 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13089 13089 (11 / 1000) ≤
    (0.008355131413 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13089) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.407167607628 : ℝ) ≤ √(13089 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13089)
  have hdiv : K / √(13089 : ℝ) ≤ K / 114.407167607628 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.407167607628 ≤ (0.008355131413 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13089.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13089 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13089 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13089 := gPlus_lower 13089
end BstLean.Part269.N13089

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13089
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035268444528 : ℝ) ≤ wn 13089 := by
  have hn : √(13089 : ℝ) ≤ 114.407167607629 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13089 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.407167607629 ≤ 2 / √(13089 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244267473 : ℝ) ≤ rhoBar 13089 BstLean.Part154.csC ∧
    rhoBar 13089 BstLean.Part154.csC ≤ 0.000244267851 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035268444528 : ℝ) / (1.295212 * 13089) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035268444529 : ℝ) / (1.29521 * 13089) := by gcongr
      _ ≤ (0.000244267851 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13089 BstLean.Part154.csC) ≤ 0.000977131071 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13089 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13089 BstLean.Part154.csC) (piBar (rhoBar 13089 BstLean.Part154.csC)) ≤ 0.000186573170 ∧
    cc1 (rhoBar 13089 BstLean.Part154.csC) (piBar (rhoBar 13089 BstLean.Part154.csC)) ≤ 0.000118717801 ∧
    cc2 (rhoBar 13089 BstLean.Part154.csC) ≤ 0.000068916659 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13089 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13089 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13089 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13089 BstLean.Part154.csC * nuR (rhoBar 13089 BstLean.Part154.csC)) ≤ 0.000488550619 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244267851 : ℝ) * 0.000977131071 := by gcongr
      _ ≤ (0.000488550619 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13089 BstLean.Part154.csC) * nuR (rhoBar 13089 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000977131071 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13089 BstLean.Part154.csC) * rhoBar 13089 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244267851 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244267851 / 2 + 0.399 * 0.000977131071 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186573170 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488550619 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118717801 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244267851 / 1.414213562 := by gcongr
      _ ≤ (0.000068916659 : ℝ) := by norm_num

end BstLean.Part269.N13089

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13089
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13089 BstLean.Part154.csC) (piBar (rhoBar 13089 BstLean.Part154.csC)) ≤ 1.50326E-7 := by
  have hr0 : 0 ≤ rhoBar 13089 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13089 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13089 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13089 BstLean.Part154.csC) (piBar (rhoBar 13089 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13089 BstLean.Part154.csC) (piBar (rhoBar 13089 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13089 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186573170 : ℝ) ^ 2 + 0.000118717801 ^ 2 + 3 * 0.000068916659 ^ 2 +
        2 * 0.797885 * 0.000186573170 * 0.000118717801 + 2 * 0.000186573170 * 0.000068916659 +
        4 * 0.797885 * 0.000118717801 * 0.000068916659 := by gcongr
    _ ≤ (1.50326E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13089 BstLean.Part154.csC Θ ≤ 0.002548481176 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13089 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13089 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13089 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13089 BstLean.Part154.csC) (piBar (rhoBar 13089 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13089 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035268444529 * 1.50326E-7 / (0.000244267473 : ℝ) := by gcongr
    _ ≤ 0.002548481176 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13089 BstLean.Part154.csC Θ ≤ 0.002826199318 + 0.000643960892 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13089 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13089 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13089 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035268444529 : ℝ) * ((2 * Θ * 0.000244267851 +
        (6863 / 10000) * 0.000244267851 * 13089 * 0.000977131071) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002826199318 + 0.000643960892 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13089 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13089 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13089 0.011 Θ ∧ gammaRatio 13089 0.011 Θ ≤ 0.000083972971 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13089 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035268444529 : ℝ) * 0.525 / ((1 - 0.011) * 13089) := by gcongr
      _ ≤ (0.000083972971 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13089 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13089 0.011 Θ) :=
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
    badAllowance 13089 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13089 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13089 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13089 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13089 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13089 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13089 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13089 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13089 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13089 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13089 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035268444529 : ℝ) * 13089 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13089 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003174451666 + 0.003192442068 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13089

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13089
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13089 BstLean.Part154.csC) (piBar (rhoBar 13089 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13089 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13089 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13089 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13089 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13089 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13089 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13089 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13089 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13089 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13089 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13089 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13089 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13089 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13089 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051690130616 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13089) ≤ 0.010438485683 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13089 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035268444529)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010438485683 + 2 * 0.737676 / 13089) := by gcongr
    _ ≤ (0.051690130616 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13089 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13089

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13089
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520637206 : ℝ) ≤ plow 13089 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13089) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052357083752)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337952618) : eMP 13089 0.011 xi bn ≤ 0.001152362829 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13089 : ℝ) * (1 - 0.011))) ≤ 0.000569828213 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001337952618 / (13089 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569828213 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569828213 : ℝ) + 3.141593 * 0.052357083752 / (13089 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001152362829 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052357083752)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337952618) : PiBarMP 13089 12 0.011 xi bn ≤ 0.158812974156 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13089 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036578034639 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.776188194191 : ℝ) ≤ √((13089 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.407167607628 : ℝ) ≤ √(13089 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13089) ≤ 0.121779155573 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036578034639 + 0.052357083752 * 1.772454 / (2 * (113.776188194191 : ℝ))) * (1 + 0.001152362829) +
        8 / (13089 * 114.407167607628) + 0.121779155573 := by gcongr
    _ ≤ (0.158812974156 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052357083752)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337952618) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280506834010) :
    parallelOracle 13089 0.011 xi bn cd ≤ 0.159773810441 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13089 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13089 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520637206 : ℝ) ≤ plow 13089 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.407167607628 : ℝ) ≤ √(13089 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280506834010 : ℝ) / (2 * 0.560520637206 * 114.407167607628)) * 0.158812974156 +
        0.280506834010 ^ 2 / (2 * 0.560520637206 * 114.407167607628) := by gcongr
    _ ≤ (0.159773810441 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052357083752) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337952618)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280506834010) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13089 13089 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520637206 : ℝ) ≤ plow 13089 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.407167607628 : ℝ) ≤ √(13089 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13089 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13089 Θ 1.22 ≤ 0.011591061363 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.407167607628 := by gcongr <;> linarith
      _ ≤ (0.011591061363 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13089 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13089 13089 0.011 ≤ 0.008355131413 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13089 13089 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13089 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13089 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13089 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13089 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159773810441 + 0.011591061363 + (0.008355131413 : ℝ) *
        (1 + 2 * (0.280506834010 + 0.011591061363) / (0.560520637206 * 114.407167607628))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13089]

end BstLean.Part269.N13089

/-! The original eight local profiles supply actual 13089 moment certificates. -/
namespace BstLean.Part269.N13089
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13089 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13089 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13089 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052357083752 ∧
    0 ≤ bN 13089 BstLean.Part154.csC (groupTheta g) ∧ bN 13089 BstLean.Part154.csC (groupTheta g) ≤ 0.001337952618 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13089 13089 0.011
      (momentAllowance 13089 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13089 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13089 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13089 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13089 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13089 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228816703394 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13089 0.011
      (momentAllowance 13089 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13089 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13089
/-! The actual computed-centre upper energy formula at 13089. -/
namespace BstLean.Part269.N13089
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13089

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13089
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13089)
open BstLean.Part268 (cell13089)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084430171228
  | 2 => 0.085355877365
  | 3 => 0.086277350654
  | 4 => 0.087195451327
  | 5 => 0.088111235924
  | 6 => 0.089025988419
  | 7 => 0.089941254648
  | 8 => 0.090858880154
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13089 13089 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13089 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003177634099 + 0.003195984085 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S29.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13089

/-! Actual upper energy certificates on all 43 source endpoints at 13089. -/
namespace BstLean.Part269.N13089
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13089)
open BstLean.Part268 (cell13089)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13089 (gMinus 13089) (1 - (cell13089 i).lower) ≤ 1 ∧
    energyUpper 13089 (gMinus 13089) (BstLean.Part211.gPlus 13089)
      (finiteEnergy 13089 13089 0.011) (1 - (cell13089 i).lower) ≤
      (cell13089 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨10,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨11,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨12,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨13,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨14,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨15,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨16,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨17,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨18,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨19,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨20,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨21,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨22,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨23,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨24,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨25,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨26,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨27,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨28,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨29,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨30,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨31,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨32,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨33,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨34,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨35,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨36,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨37,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨38,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨39,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨40,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨41,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨42,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨43,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨44,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨45,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨46,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨47,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨48,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨49,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨50,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨51,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13089) (by norm_num)
        (q := 1 - (cell13089 ⟨52,by decide⟩).lower)
        (by norm_num [cell13089]) (by norm_num [cell13089])
      exact ⟨E.1,E.2.trans (by norm_num [cell13089])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13089

/-! Source-cell containment and simple scalar guards at 13089. -/
namespace BstLean.Part269.N13089
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13089)
open BstLean.Part268 (cell13089)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13089 ⟨10,by decide⟩).lower ∧ (cell13089 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13089 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13089 ⟨11,by decide⟩).lower ∧ (cell13089 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13089 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13089 ⟨12,by decide⟩).lower ∧ (cell13089 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13089 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13089 ⟨13,by decide⟩).lower ∧ (cell13089 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13089 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13089 ⟨14,by decide⟩).lower ∧ (cell13089 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13089 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13089 ⟨15,by decide⟩).lower ∧ (cell13089 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13089 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13089 ⟨16,by decide⟩).lower ∧ (cell13089 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13089 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13089 ⟨17,by decide⟩).lower ∧ (cell13089 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13089 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13089 ⟨18,by decide⟩).lower ∧ (cell13089 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13089 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13089 ⟨19,by decide⟩).lower ∧ (cell13089 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13089 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13089 ⟨20,by decide⟩).lower ∧ (cell13089 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13089 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13089 ⟨21,by decide⟩).lower ∧ (cell13089 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13089 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13089 ⟨22,by decide⟩).lower ∧ (cell13089 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13089 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13089 ⟨23,by decide⟩).lower ∧ (cell13089 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13089 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13089 ⟨24,by decide⟩).lower ∧ (cell13089 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13089 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13089 ⟨25,by decide⟩).lower ∧ (cell13089 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13089 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13089 ⟨26,by decide⟩).lower ∧ (cell13089 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13089 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13089 ⟨27,by decide⟩).lower ∧ (cell13089 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13089 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13089 ⟨28,by decide⟩).lower ∧ (cell13089 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13089 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13089 ⟨29,by decide⟩).lower ∧ (cell13089 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13089 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13089 ⟨30,by decide⟩).lower ∧ (cell13089 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13089 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13089 ⟨31,by decide⟩).lower ∧ (cell13089 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13089 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13089 ⟨32,by decide⟩).lower ∧ (cell13089 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13089 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13089 ⟨33,by decide⟩).lower ∧ (cell13089 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13089 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13089 ⟨34,by decide⟩).lower ∧ (cell13089 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13089 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13089 ⟨35,by decide⟩).lower ∧ (cell13089 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13089 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13089 ⟨36,by decide⟩).lower ∧ (cell13089 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13089 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13089 ⟨37,by decide⟩).lower ∧ (cell13089 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13089 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13089 ⟨38,by decide⟩).lower ∧ (cell13089 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13089 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13089 ⟨39,by decide⟩).lower ∧ (cell13089 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13089 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13089 ⟨40,by decide⟩).lower ∧ (cell13089 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13089 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13089 ⟨41,by decide⟩).lower ∧ (cell13089 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13089 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13089 ⟨42,by decide⟩).lower ∧ (cell13089 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13089 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13089 ⟨43,by decide⟩).lower ∧ (cell13089 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13089 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13089 ⟨44,by decide⟩).lower ∧ (cell13089 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13089 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13089 ⟨45,by decide⟩).lower ∧ (cell13089 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13089 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13089 ⟨46,by decide⟩).lower ∧ (cell13089 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13089 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13089 ⟨47,by decide⟩).lower ∧ (cell13089 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13089 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13089 ⟨48,by decide⟩).lower ∧ (cell13089 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13089 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13089 ⟨49,by decide⟩).lower ∧ (cell13089 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13089 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13089 ⟨50,by decide⟩).lower ∧ (cell13089 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13089 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13089 ⟨51,by decide⟩).lower ∧ (cell13089 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13089 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13089 ⟨52,by decide⟩).lower ∧ (cell13089 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13089 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13089 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13089 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13089,cell13089,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13089 i).lower ∧
    (cell13089 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13089 i).upper ≤ (0.532 : ℝ) ∧
    (cell13089 i).centre ≤ (0.1 : ℝ) ∧ (cell13089 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13089 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13089 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13089

/-! The local source numeric instances at 13089 have no network premises. -/
namespace BstLean.Part269.N13089
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13089)
open BstLean.Part268 (cell13089)

noncomputable def sourceNumerics13089 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13089 (cell13089 i)
      scalarRow13089.M scalarRow13089.H scalarRow13089.xi := by
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
    energy_allowance := scalarRow13089.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13089]
    centre_nonneg := (scalarRow13089.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13089])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13089
/-! Actual 13090 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13090
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13090 ≤ (1.035267085678 : ℝ) := by
  have hr : (114.411537879708 : ℝ) ≤ √(13090 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.411537879708 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13090 13090 (11 / 1000) ≤
    (0.008354812262 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13090) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.411537879708 : ℝ) ≤ √(13090 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13090)
  have hdiv : K / √(13090 : ℝ) ≤ K / 114.411537879708 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.411537879708 ≤ (0.008354812262 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13090.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13090 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13090 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13090 := gPlus_lower 13090
end BstLean.Part269.N13090

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13090
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035267085677 : ℝ) ≤ wn 13090 := by
  have hn : √(13090 : ℝ) ≤ 114.411537879709 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13090 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.411537879709 ≤ 2 / √(13090 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244248492 : ℝ) ≤ rhoBar 13090 BstLean.Part154.csC ∧
    rhoBar 13090 BstLean.Part154.csC ≤ 0.000244248870 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035267085677 : ℝ) / (1.295212 * 13090) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035267085678 : ℝ) / (1.29521 * 13090) := by gcongr
      _ ≤ (0.000244248870 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13090 BstLean.Part154.csC) ≤ 0.000977055138 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13090 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13090 BstLean.Part154.csC) (piBar (rhoBar 13090 BstLean.Part154.csC)) ≤ 0.000186558672 ∧
    cc1 (rhoBar 13090 BstLean.Part154.csC) (piBar (rhoBar 13090 BstLean.Part154.csC)) ≤ 0.000118708576 ∧
    cc2 (rhoBar 13090 BstLean.Part154.csC) ≤ 0.000068911303 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13090 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13090 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13090 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13090 BstLean.Part154.csC * nuR (rhoBar 13090 BstLean.Part154.csC)) ≤ 0.000488512655 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244248870 : ℝ) * 0.000977055138 := by gcongr
      _ ≤ (0.000488512655 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13090 BstLean.Part154.csC) * nuR (rhoBar 13090 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000977055138 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13090 BstLean.Part154.csC) * rhoBar 13090 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244248870 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244248870 / 2 + 0.399 * 0.000977055138 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186558672 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488512655 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118708576 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244248870 / 1.414213562 := by gcongr
      _ ≤ (0.000068911303 : ℝ) := by norm_num

end BstLean.Part269.N13090

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13090
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13090 BstLean.Part154.csC) (piBar (rhoBar 13090 BstLean.Part154.csC)) ≤ 1.50303E-7 := by
  have hr0 : 0 ≤ rhoBar 13090 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13090 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13090 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13090 BstLean.Part154.csC) (piBar (rhoBar 13090 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13090 BstLean.Part154.csC) (piBar (rhoBar 13090 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13090 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186558672 : ℝ) ^ 2 + 0.000118708576 ^ 2 + 3 * 0.000068911303 ^ 2 +
        2 * 0.797885 * 0.000186558672 * 0.000118708576 + 2 * 0.000186558672 * 0.000068911303 +
        4 * 0.797885 * 0.000118708576 * 0.000068911303 := by gcongr
    _ ≤ (1.50303E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13090 BstLean.Part154.csC Θ ≤ 0.002548285929 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13090 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13090 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13090 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13090 BstLean.Part154.csC) (piBar (rhoBar 13090 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13090 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035267085678 * 1.50303E-7 / (0.000244248492 : ℝ) := by gcongr
    _ ≤ 0.002548285929 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13090 BstLean.Part154.csC Θ ≤ 0.002825972278 + 0.000643910007 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13090 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13090 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13090 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035267085678 : ℝ) * ((2 * Θ * 0.000244248870 +
        (6863 / 10000) * 0.000244248870 * 13090 * 0.000977055138) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002825972278 + 0.000643910007 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13090 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13090 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13090 0.011 Θ ∧ gammaRatio 13090 0.011 Θ ≤ 0.000083966446 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13090 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035267085678 : ℝ) * 0.525 / ((1 - 0.011) * 13090) := by gcongr
      _ ≤ (0.000083966446 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13090 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13090 0.011 Θ) :=
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
    badAllowance 13090 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13090 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13090 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13090 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13090 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13090 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13090 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13090 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13090 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13090 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13090 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035267085678 : ℝ) * 13090 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13090 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003174224626 + 0.003192195936 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13090

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13090
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13090 BstLean.Part154.csC) (piBar (rhoBar 13090 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13090 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13090 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13090 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13090 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13090 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13090 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13090 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13090 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13090 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13090 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13090 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13090 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13090 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13090 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051688135076 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13090) ≤ 0.010438086956 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13090 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035267085678)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010438086956 + 2 * 0.737676 / 13090) := by gcongr
    _ ≤ (0.051688135076 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13090 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13090

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13090
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520679778 : ℝ) ≤ plow 13090 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13090) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052356727493)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337850113) : eMP 13090 0.011 xi bn ≤ 0.001152274584 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13090 : ℝ) * (1 - 0.011))) ≤ 0.000569784619 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001337850113 / (13090 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569784619 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569784619 : ℝ) + 3.141593 * 0.052356727493 / (13090 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001152274584 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052356727493)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337850113) : PiBarMP 13090 12 0.011 xi bn ≤ 0.158806897383 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13090 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036576633430 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.780534363308 : ℝ) ≤ √((13090 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.411537879708 : ℝ) ≤ √(13090 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13090) ≤ 0.121774503874 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036576633430 + 0.052356727493 * 1.772454 / (2 * (113.780534363308 : ℝ))) * (1 + 0.001152274584) +
        8 / (13090 * 114.411537879708) + 0.121774503874 := by gcongr
    _ ≤ (0.158806897383 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052356727493)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337850113) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280504059988) :
    parallelOracle 13090 0.011 xi bn cd ≤ 0.159767668035 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13090 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13090 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520679778 : ℝ) ≤ plow 13090 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.411537879708 : ℝ) ≤ √(13090 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280504059988 : ℝ) / (2 * 0.560520679778 * 114.411537879708)) * 0.158806897383 +
        0.280504059988 ^ 2 / (2 * 0.560520679778 * 114.411537879708) := by gcongr
    _ ≤ (0.159767668035 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052356727493) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337850113)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280504059988) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13090 13090 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520679778 : ℝ) ≤ plow 13090 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.411537879708 : ℝ) ≤ √(13090 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13090 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13090 Θ 1.22 ≤ 0.011590618609 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.411537879708 := by gcongr <;> linarith
      _ ≤ (0.011590618609 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13090 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13090 13090 0.011 ≤ 0.008354812262 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13090 13090 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13090 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13090 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13090 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13090 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159767668035 + 0.011590618609 + (0.008354812262 : ℝ) *
        (1 + 2 * (0.280504059988 + 0.011590618609) / (0.560520679778 * 114.411537879708))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13090]

end BstLean.Part269.N13090

/-! The original eight local profiles supply actual 13090 moment certificates. -/
namespace BstLean.Part269.N13090
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13090 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13090 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13090 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052356727493 ∧
    0 ≤ bN 13090 BstLean.Part154.csC (groupTheta g) ∧ bN 13090 BstLean.Part154.csC (groupTheta g) ≤ 0.001337850113 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13090 13090 0.011
      (momentAllowance 13090 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13090 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13090 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13090 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13090 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13090 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228815924912 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13090 0.011
      (momentAllowance 13090 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13090 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13090
/-! The actual computed-centre upper energy formula at 13090. -/
namespace BstLean.Part269.N13090
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13090

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13090
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13090)
open BstLean.Part268 (cell13090)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084427622011
  | 2 => 0.085353295999
  | 3 => 0.086274732460
  | 4 => 0.087192790517
  | 5 => 0.088108525396
  | 6 => 0.089023219522
  | 7 => 0.089938416921
  | 8 => 0.090855961034
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13090 13090 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13090 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003177634099 + 0.003195984085 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S29.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13090

/-! Actual upper energy certificates on all 43 source endpoints at 13090. -/
namespace BstLean.Part269.N13090
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13090)
open BstLean.Part268 (cell13090)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13090 (gMinus 13090) (1 - (cell13090 i).lower) ≤ 1 ∧
    energyUpper 13090 (gMinus 13090) (BstLean.Part211.gPlus 13090)
      (finiteEnergy 13090 13090 0.011) (1 - (cell13090 i).lower) ≤
      (cell13090 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨10,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨11,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨12,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨13,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨14,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨15,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨16,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨17,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨18,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨19,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨20,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨21,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨22,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨23,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨24,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨25,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨26,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨27,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨28,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨29,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨30,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨31,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨32,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨33,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨34,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨35,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨36,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨37,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨38,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨39,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨40,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨41,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨42,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨43,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨44,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨45,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨46,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨47,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨48,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨49,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨50,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨51,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13090) (by norm_num)
        (q := 1 - (cell13090 ⟨52,by decide⟩).lower)
        (by norm_num [cell13090]) (by norm_num [cell13090])
      exact ⟨E.1,E.2.trans (by norm_num [cell13090])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13090

/-! Source-cell containment and simple scalar guards at 13090. -/
namespace BstLean.Part269.N13090
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13090)
open BstLean.Part268 (cell13090)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13090 ⟨10,by decide⟩).lower ∧ (cell13090 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13090 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13090 ⟨11,by decide⟩).lower ∧ (cell13090 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13090 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13090 ⟨12,by decide⟩).lower ∧ (cell13090 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13090 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13090 ⟨13,by decide⟩).lower ∧ (cell13090 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13090 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13090 ⟨14,by decide⟩).lower ∧ (cell13090 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13090 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13090 ⟨15,by decide⟩).lower ∧ (cell13090 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13090 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13090 ⟨16,by decide⟩).lower ∧ (cell13090 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13090 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13090 ⟨17,by decide⟩).lower ∧ (cell13090 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13090 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13090 ⟨18,by decide⟩).lower ∧ (cell13090 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13090 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13090 ⟨19,by decide⟩).lower ∧ (cell13090 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13090 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13090 ⟨20,by decide⟩).lower ∧ (cell13090 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13090 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13090 ⟨21,by decide⟩).lower ∧ (cell13090 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13090 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13090 ⟨22,by decide⟩).lower ∧ (cell13090 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13090 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13090 ⟨23,by decide⟩).lower ∧ (cell13090 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13090 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13090 ⟨24,by decide⟩).lower ∧ (cell13090 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13090 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13090 ⟨25,by decide⟩).lower ∧ (cell13090 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13090 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13090 ⟨26,by decide⟩).lower ∧ (cell13090 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13090 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13090 ⟨27,by decide⟩).lower ∧ (cell13090 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13090 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13090 ⟨28,by decide⟩).lower ∧ (cell13090 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13090 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13090 ⟨29,by decide⟩).lower ∧ (cell13090 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13090 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13090 ⟨30,by decide⟩).lower ∧ (cell13090 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13090 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13090 ⟨31,by decide⟩).lower ∧ (cell13090 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13090 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13090 ⟨32,by decide⟩).lower ∧ (cell13090 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13090 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13090 ⟨33,by decide⟩).lower ∧ (cell13090 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13090 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13090 ⟨34,by decide⟩).lower ∧ (cell13090 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13090 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13090 ⟨35,by decide⟩).lower ∧ (cell13090 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13090 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13090 ⟨36,by decide⟩).lower ∧ (cell13090 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13090 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13090 ⟨37,by decide⟩).lower ∧ (cell13090 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13090 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13090 ⟨38,by decide⟩).lower ∧ (cell13090 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13090 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13090 ⟨39,by decide⟩).lower ∧ (cell13090 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13090 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13090 ⟨40,by decide⟩).lower ∧ (cell13090 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13090 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13090 ⟨41,by decide⟩).lower ∧ (cell13090 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13090 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13090 ⟨42,by decide⟩).lower ∧ (cell13090 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13090 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13090 ⟨43,by decide⟩).lower ∧ (cell13090 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13090 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13090 ⟨44,by decide⟩).lower ∧ (cell13090 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13090 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13090 ⟨45,by decide⟩).lower ∧ (cell13090 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13090 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13090 ⟨46,by decide⟩).lower ∧ (cell13090 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13090 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13090 ⟨47,by decide⟩).lower ∧ (cell13090 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13090 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13090 ⟨48,by decide⟩).lower ∧ (cell13090 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13090 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13090 ⟨49,by decide⟩).lower ∧ (cell13090 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13090 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13090 ⟨50,by decide⟩).lower ∧ (cell13090 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13090 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13090 ⟨51,by decide⟩).lower ∧ (cell13090 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13090 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13090 ⟨52,by decide⟩).lower ∧ (cell13090 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13090 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13090 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13090 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13090,cell13090,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13090 i).lower ∧
    (cell13090 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13090 i).upper ≤ (0.532 : ℝ) ∧
    (cell13090 i).centre ≤ (0.1 : ℝ) ∧ (cell13090 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13090 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13090 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13090

/-! The local source numeric instances at 13090 have no network premises. -/
namespace BstLean.Part269.N13090
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13090)
open BstLean.Part268 (cell13090)

noncomputable def sourceNumerics13090 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13090 (cell13090 i)
      scalarRow13090.M scalarRow13090.H scalarRow13090.xi := by
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
    energy_allowance := scalarRow13090.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13090]
    centre_nonneg := (scalarRow13090.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13090])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13090
/-! Actual 13091 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13091
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13091 ≤ (1.035265726984 : ℝ) := by
  have hr : (114.415907984860 : ℝ) ≤ √(13091 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.415907984860 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13091 13091 (11 / 1000) ≤
    (0.008354493149 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13091) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.415907984860 : ℝ) ≤ √(13091 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13091)
  have hdiv : K / √(13091 : ℝ) ≤ K / 114.415907984860 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.415907984860 ≤ (0.008354493149 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13091.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13091 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13091 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13091 := gPlus_lower 13091
end BstLean.Part269.N13091

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13091
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035265726983 : ℝ) ≤ wn 13091 := by
  have hn : √(13091 : ℝ) ≤ 114.415907984861 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13091 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.415907984861 ≤ 2 / √(13091 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244229514 : ℝ) ≤ rhoBar 13091 BstLean.Part154.csC ∧
    rhoBar 13091 BstLean.Part154.csC ≤ 0.000244229892 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035265726983 : ℝ) / (1.295212 * 13091) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035265726984 : ℝ) / (1.29521 * 13091) := by gcongr
      _ ≤ (0.000244229892 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13091 BstLean.Part154.csC) ≤ 0.000976979217 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13091 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13091 BstLean.Part154.csC) (piBar (rhoBar 13091 BstLean.Part154.csC)) ≤ 0.000186544176 ∧
    cc1 (rhoBar 13091 BstLean.Part154.csC) (piBar (rhoBar 13091 BstLean.Part154.csC)) ≤ 0.000118699352 ∧
    cc2 (rhoBar 13091 BstLean.Part154.csC) ≤ 0.000068905949 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13091 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13091 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13091 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13091 BstLean.Part154.csC * nuR (rhoBar 13091 BstLean.Part154.csC)) ≤ 0.000488474697 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244229892 : ℝ) * 0.000976979217 := by gcongr
      _ ≤ (0.000488474697 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13091 BstLean.Part154.csC) * nuR (rhoBar 13091 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000976979217 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13091 BstLean.Part154.csC) * rhoBar 13091 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244229892 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244229892 / 2 + 0.399 * 0.000976979217 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186544176 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488474697 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118699352 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244229892 / 1.414213562 := by gcongr
      _ ≤ (0.000068905949 : ℝ) := by norm_num

end BstLean.Part269.N13091

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13091
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13091 BstLean.Part154.csC) (piBar (rhoBar 13091 BstLean.Part154.csC)) ≤ 1.50279E-7 := by
  have hr0 : 0 ≤ rhoBar 13091 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13091 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13091 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13091 BstLean.Part154.csC) (piBar (rhoBar 13091 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13091 BstLean.Part154.csC) (piBar (rhoBar 13091 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13091 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186544176 : ℝ) ^ 2 + 0.000118699352 ^ 2 + 3 * 0.000068905949 ^ 2 +
        2 * 0.797885 * 0.000186544176 * 0.000118699352 + 2 * 0.000186544176 * 0.000068905949 +
        4 * 0.797885 * 0.000118699352 * 0.000068905949 := by gcongr
    _ ≤ (1.50279E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13091 BstLean.Part154.csC Θ ≤ 0.002548073665 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13091 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13091 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13091 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13091 BstLean.Part154.csC) (piBar (rhoBar 13091 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13091 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035265726984 * 1.50279E-7 / (0.000244229514 : ℝ) := by gcongr
    _ ≤ 0.002548073665 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13091 BstLean.Part154.csC Θ ≤ 0.002825745275 + 0.000643859131 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13091 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13091 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13091 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035265726984 : ℝ) * ((2 * Θ * 0.000244229892 +
        (6863 / 10000) * 0.000244229892 * 13091 * 0.000976979217) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002825745275 + 0.000643859131 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13091 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13091 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13091 0.011 Θ ∧ gammaRatio 13091 0.011 Θ ≤ 0.000083959922 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13091 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035265726984 : ℝ) * 0.525 / ((1 - 0.011) * 13091) := by gcongr
      _ ≤ (0.000083959922 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13091 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13091 0.011 Θ) :=
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
    badAllowance 13091 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13091 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13091 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13091 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13091 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13091 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13091 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13091 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13091 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13091 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13091 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035265726984 : ℝ) * 13091 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13091 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003173997623 + 0.003191932796 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13091

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13091
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13091 BstLean.Part154.csC) (piBar (rhoBar 13091 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13091 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13091 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13091 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13091 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13091 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13091 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13091 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13091 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13091 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13091 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13091 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13091 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13091 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13091 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051686139762 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13091) ≤ 0.010437688274 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13091 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035265726984)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010437688274 + 2 * 0.737676 / 13091) := by gcongr
    _ ≤ (0.051686139762 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13091 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13091

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13091
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520722343 : ℝ) ≤ plow 13091 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13091) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052356362341)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337738675) : eMP 13091 0.011 xi bn ≤ 0.001152182539 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13091 : ℝ) * (1 - 0.011))) ≤ 0.000569739126 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001337738675 / (13091 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569739126 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569739126 : ℝ) + 3.141593 * 0.052356362341 / (13091 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001152182539 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052356362341)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337738675) : PiBarMP 13091 12 0.011 xi bn ≤ 0.158800698623 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13091 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036575110048 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.784880366417 : ℝ) ≤ √((13091 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.415907984860 : ℝ) ≤ √(13091 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13091) ≤ 0.121769852708 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036575110048 + 0.052356362341 * 1.772454 / (2 * (113.784880366417 : ℝ))) * (1 + 0.001152182539) +
        8 / (13091 * 114.415907984860) + 0.121769852708 := by gcongr
    _ ≤ (0.158800698623 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052356362341)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337738675) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280501266756) :
    parallelOracle 13091 0.011 xi bn cd ≤ 0.159761403274 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13091 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13091 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520722343 : ℝ) ≤ plow 13091 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.415907984860 : ℝ) ≤ √(13091 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280501266756 : ℝ) / (2 * 0.560520722343 * 114.415907984860)) * 0.158800698623 +
        0.280501266756 ^ 2 / (2 * 0.560520722343 * 114.415907984860) := by gcongr
    _ ≤ (0.159761403274 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052356362341) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337738675)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280501266756) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13091 13091 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520722343 : ℝ) ≤ plow 13091 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.415907984860 : ℝ) ≤ √(13091 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13091 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13091 Θ 1.22 ≤ 0.011590175907 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.415907984860 := by gcongr <;> linarith
      _ ≤ (0.011590175907 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13091 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13091 13091 0.011 ≤ 0.008354493149 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13091 13091 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13091 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13091 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13091 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13091 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159761403274 + 0.011590175907 + (0.008354493149 : ℝ) *
        (1 + 2 * (0.280501266756 + 0.011590175907) / (0.560520722343 * 114.415907984860))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13091]

end BstLean.Part269.N13091

/-! The original eight local profiles supply actual 13091 moment certificates. -/
namespace BstLean.Part269.N13091
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13091 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13091 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13091 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052356362341 ∧
    0 ≤ bN 13091 BstLean.Part154.csC (groupTheta g) ∧ bN 13091 BstLean.Part154.csC (groupTheta g) ≤ 0.001337738675 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13091 13091 0.011
      (momentAllowance 13091 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13091 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13091 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13091 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13091 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13091 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228815126994 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13091 0.011
      (momentAllowance 13091 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13091 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13091
/-! The actual computed-centre upper energy formula at 13091. -/
namespace BstLean.Part269.N13091
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13091

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13091
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13091)
open BstLean.Part268 (cell13091)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084425073539
  | 2 => 0.085350715402
  | 3 => 0.086272115067
  | 4 => 0.087190130548
  | 5 => 0.088105815756
  | 6 => 0.089020451571
  | 7 => 0.089935580212
  | 8 => 0.090853043018
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13091 13091 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13091 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003177634099 + 0.003195984085 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S29.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13091

/-! Actual upper energy certificates on all 43 source endpoints at 13091. -/
namespace BstLean.Part269.N13091
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13091)
open BstLean.Part268 (cell13091)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13091 (gMinus 13091) (1 - (cell13091 i).lower) ≤ 1 ∧
    energyUpper 13091 (gMinus 13091) (BstLean.Part211.gPlus 13091)
      (finiteEnergy 13091 13091 0.011) (1 - (cell13091 i).lower) ≤
      (cell13091 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨10,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨11,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨12,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨13,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨14,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨15,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨16,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨17,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨18,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨19,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨20,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨21,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨22,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨23,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨24,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨25,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨26,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨27,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨28,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨29,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨30,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨31,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨32,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨33,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨34,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨35,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨36,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨37,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨38,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨39,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨40,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨41,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨42,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨43,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨44,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨45,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨46,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨47,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨48,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨49,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨50,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨51,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13091) (by norm_num)
        (q := 1 - (cell13091 ⟨52,by decide⟩).lower)
        (by norm_num [cell13091]) (by norm_num [cell13091])
      exact ⟨E.1,E.2.trans (by norm_num [cell13091])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13091

/-! Source-cell containment and simple scalar guards at 13091. -/
namespace BstLean.Part269.N13091
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13091)
open BstLean.Part268 (cell13091)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13091 ⟨10,by decide⟩).lower ∧ (cell13091 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13091 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13091 ⟨11,by decide⟩).lower ∧ (cell13091 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13091 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13091 ⟨12,by decide⟩).lower ∧ (cell13091 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13091 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13091 ⟨13,by decide⟩).lower ∧ (cell13091 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13091 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13091 ⟨14,by decide⟩).lower ∧ (cell13091 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13091 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13091 ⟨15,by decide⟩).lower ∧ (cell13091 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13091 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13091 ⟨16,by decide⟩).lower ∧ (cell13091 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13091 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13091 ⟨17,by decide⟩).lower ∧ (cell13091 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13091 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13091 ⟨18,by decide⟩).lower ∧ (cell13091 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13091 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13091 ⟨19,by decide⟩).lower ∧ (cell13091 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13091 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13091 ⟨20,by decide⟩).lower ∧ (cell13091 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13091 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13091 ⟨21,by decide⟩).lower ∧ (cell13091 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13091 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13091 ⟨22,by decide⟩).lower ∧ (cell13091 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13091 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13091 ⟨23,by decide⟩).lower ∧ (cell13091 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13091 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13091 ⟨24,by decide⟩).lower ∧ (cell13091 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13091 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13091 ⟨25,by decide⟩).lower ∧ (cell13091 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13091 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13091 ⟨26,by decide⟩).lower ∧ (cell13091 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13091 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13091 ⟨27,by decide⟩).lower ∧ (cell13091 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13091 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13091 ⟨28,by decide⟩).lower ∧ (cell13091 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13091 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13091 ⟨29,by decide⟩).lower ∧ (cell13091 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13091 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13091 ⟨30,by decide⟩).lower ∧ (cell13091 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13091 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13091 ⟨31,by decide⟩).lower ∧ (cell13091 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13091 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13091 ⟨32,by decide⟩).lower ∧ (cell13091 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13091 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13091 ⟨33,by decide⟩).lower ∧ (cell13091 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13091 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13091 ⟨34,by decide⟩).lower ∧ (cell13091 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13091 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13091 ⟨35,by decide⟩).lower ∧ (cell13091 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13091 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13091 ⟨36,by decide⟩).lower ∧ (cell13091 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13091 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13091 ⟨37,by decide⟩).lower ∧ (cell13091 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13091 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13091 ⟨38,by decide⟩).lower ∧ (cell13091 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13091 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13091 ⟨39,by decide⟩).lower ∧ (cell13091 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13091 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13091 ⟨40,by decide⟩).lower ∧ (cell13091 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13091 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13091 ⟨41,by decide⟩).lower ∧ (cell13091 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13091 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13091 ⟨42,by decide⟩).lower ∧ (cell13091 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13091 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13091 ⟨43,by decide⟩).lower ∧ (cell13091 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13091 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13091 ⟨44,by decide⟩).lower ∧ (cell13091 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13091 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13091 ⟨45,by decide⟩).lower ∧ (cell13091 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13091 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13091 ⟨46,by decide⟩).lower ∧ (cell13091 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13091 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13091 ⟨47,by decide⟩).lower ∧ (cell13091 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13091 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13091 ⟨48,by decide⟩).lower ∧ (cell13091 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13091 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13091 ⟨49,by decide⟩).lower ∧ (cell13091 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13091 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13091 ⟨50,by decide⟩).lower ∧ (cell13091 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13091 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13091 ⟨51,by decide⟩).lower ∧ (cell13091 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13091 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13091 ⟨52,by decide⟩).lower ∧ (cell13091 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13091 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13091 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13091 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13091,cell13091,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13091 i).lower ∧
    (cell13091 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13091 i).upper ≤ (0.532 : ℝ) ∧
    (cell13091 i).centre ≤ (0.1 : ℝ) ∧ (cell13091 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13091 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13091 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13091

/-! The local source numeric instances at 13091 have no network premises. -/
namespace BstLean.Part269.N13091
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13091)
open BstLean.Part268 (cell13091)

noncomputable def sourceNumerics13091 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13091 (cell13091 i)
      scalarRow13091.M scalarRow13091.H scalarRow13091.xi := by
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
    energy_allowance := scalarRow13091.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13091]
    centre_nonneg := (scalarRow13091.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13091])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13091
/-! Actual 13092 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13092
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13092 ≤ (1.035264368446 : ℝ) := by
  have hr : (114.420277923102 : ℝ) ≤ √(13092 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.420277923102 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13092 13092 (11 / 1000) ≤
    (0.008354174072 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13092) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.420277923102 : ℝ) ≤ √(13092 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13092)
  have hdiv : K / √(13092 : ℝ) ≤ K / 114.420277923102 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.420277923102 ≤ (0.008354174072 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13092.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13092 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13092 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13092 := gPlus_lower 13092
end BstLean.Part269.N13092

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13092
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035264368445 : ℝ) ≤ wn 13092 := by
  have hn : √(13092 : ℝ) ≤ 114.420277923103 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13092 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.420277923103 ≤ 2 / √(13092 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244210538 : ℝ) ≤ rhoBar 13092 BstLean.Part154.csC ∧
    rhoBar 13092 BstLean.Part154.csC ≤ 0.000244210917 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035264368445 : ℝ) / (1.295212 * 13092) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035264368446 : ℝ) / (1.29521 * 13092) := by gcongr
      _ ≤ (0.000244210917 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13092 BstLean.Part154.csC) ≤ 0.000976903307 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13092 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13092 BstLean.Part154.csC) (piBar (rhoBar 13092 BstLean.Part154.csC)) ≤ 0.000186529682 ∧
    cc1 (rhoBar 13092 BstLean.Part154.csC) (piBar (rhoBar 13092 BstLean.Part154.csC)) ≤ 0.000118690129 ∧
    cc2 (rhoBar 13092 BstLean.Part154.csC) ≤ 0.000068900596 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13092 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13092 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13092 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13092 BstLean.Part154.csC * nuR (rhoBar 13092 BstLean.Part154.csC)) ≤ 0.000488436744 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244210917 : ℝ) * 0.000976903307 := by gcongr
      _ ≤ (0.000488436744 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13092 BstLean.Part154.csC) * nuR (rhoBar 13092 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000976903307 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13092 BstLean.Part154.csC) * rhoBar 13092 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244210917 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244210917 / 2 + 0.399 * 0.000976903307 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186529682 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488436744 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118690129 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244210917 / 1.414213562 := by gcongr
      _ ≤ (0.000068900596 : ℝ) := by norm_num

end BstLean.Part269.N13092

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13092
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13092 BstLean.Part154.csC) (piBar (rhoBar 13092 BstLean.Part154.csC)) ≤ 1.50256E-7 := by
  have hr0 : 0 ≤ rhoBar 13092 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13092 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13092 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13092 BstLean.Part154.csC) (piBar (rhoBar 13092 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13092 BstLean.Part154.csC) (piBar (rhoBar 13092 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13092 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186529682 : ℝ) ^ 2 + 0.000118690129 ^ 2 + 3 * 0.000068900596 ^ 2 +
        2 * 0.797885 * 0.000186529682 * 0.000118690129 + 2 * 0.000186529682 * 0.000068900596 +
        4 * 0.797885 * 0.000118690129 * 0.000068900596 := by gcongr
    _ ≤ (1.50256E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13092 BstLean.Part154.csC Θ ≤ 0.002547878306 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13092 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13092 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13092 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13092 BstLean.Part154.csC) (piBar (rhoBar 13092 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13092 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035264368446 * 1.50256E-7 / (0.000244210538 : ℝ) := by gcongr
    _ ≤ 0.002547878306 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13092 BstLean.Part154.csC Θ ≤ 0.002825518307 + 0.000643808263 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13092 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13092 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13092 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035264368446 : ℝ) * ((2 * Θ * 0.000244210917 +
        (6863 / 10000) * 0.000244210917 * 13092 * 0.000976903307) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002825518307 + 0.000643808263 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13092 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13092 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13092 0.011 Θ ∧ gammaRatio 13092 0.011 Θ ≤ 0.000083953398 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13092 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035264368446 : ℝ) * 0.525 / ((1 - 0.011) * 13092) := by gcongr
      _ ≤ (0.000083953398 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13092 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13092 0.011 Θ) :=
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
    badAllowance 13092 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13092 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13092 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13092 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13092 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13092 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13092 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13092 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13092 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13092 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13092 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035264368446 : ℝ) * 13092 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13092 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003173770655 + 0.003191686569 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13092

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13092
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13092 BstLean.Part154.csC) (piBar (rhoBar 13092 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13092 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13092 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13092 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13092 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13092 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13092 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13092 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13092 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13092 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13092 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13092 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13092 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13092 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13092 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051684144681 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13092) ≤ 0.010437289638 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13092 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035264368446)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010437289638 + 2 * 0.737676 / 13092) := by gcongr
    _ ≤ (0.051684144681 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13092 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13092

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13092
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520764902 : ℝ) ≤ plow 13092 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13092) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052356006104)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337636111) : eMP 13092 0.011 xi bn ≤ 0.001152094282 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13092 : ℝ) * (1 - 0.011))) ≤ 0.000569695526 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001337636111 / (13092 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569695526 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569695526 : ℝ) + 3.141593 * 0.052356006104 / (13092 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001152094282 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052356006104)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337636111) : PiBarMP 13092 12 0.011 xi bn ≤ 0.158794622001 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13092 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036573707920 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.789226203538 : ℝ) ≤ √((13092 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.420277923102 : ℝ) ≤ √(13092 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13092) ≤ 0.121765202075 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036573707920 + 0.052356006104 * 1.772454 / (2 * (113.789226203538 : ℝ))) * (1 + 0.001152094282) +
        8 / (13092 * 114.420277923102) + 0.121765202075 := by gcongr
    _ ≤ (0.158794622001 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052356006104)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337636111) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280498493235) :
    parallelOracle 13092 0.011 xi bn cd ≤ 0.159755261036 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13092 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13092 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520764902 : ℝ) ≤ plow 13092 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.420277923102 : ℝ) ≤ √(13092 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280498493235 : ℝ) / (2 * 0.560520764902 * 114.420277923102)) * 0.158794622001 +
        0.280498493235 ^ 2 / (2 * 0.560520764902 * 114.420277923102) := by gcongr
    _ ≤ (0.159755261036 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052356006104) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337636111)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280498493235) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13092 13092 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520764902 : ℝ) ≤ plow 13092 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.420277923102 : ℝ) ≤ √(13092 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13092 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13092 Θ 1.22 ≤ 0.011589733255 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.420277923102 := by gcongr <;> linarith
      _ ≤ (0.011589733255 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13092 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13092 13092 0.011 ≤ 0.008354174072 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13092 13092 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13092 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13092 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13092 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13092 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159755261036 + 0.011589733255 + (0.008354174072 : ℝ) *
        (1 + 2 * (0.280498493235 + 0.011589733255) / (0.560520764902 * 114.420277923102))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13092]

end BstLean.Part269.N13092

/-! The original eight local profiles supply actual 13092 moment certificates. -/
namespace BstLean.Part269.N13092
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13092 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13092 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13092 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052356006104 ∧
    0 ≤ bN 13092 BstLean.Part154.csC (groupTheta g) ∧ bN 13092 BstLean.Part154.csC (groupTheta g) ≤ 0.001337636111 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13092 13092 0.011
      (momentAllowance 13092 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13092 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13092 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13092 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13092 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13092 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228814348554 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13092 0.011
      (momentAllowance 13092 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13092 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13092
/-! The actual computed-centre upper energy formula at 13092. -/
namespace BstLean.Part269.N13092
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13092

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13092
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13092)
open BstLean.Part268 (cell13092)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084422525809
  | 2 => 0.085348135573
  | 3 => 0.086269498474
  | 4 => 0.087187471417
  | 5 => 0.088103107003
  | 6 => 0.089017684566
  | 7 => 0.089932744519
  | 8 => 0.090850126104
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13092 13092 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13092 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003177634099 + 0.003195984085 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S29.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13092

/-! Actual upper energy certificates on all 43 source endpoints at 13092. -/
namespace BstLean.Part269.N13092
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13092)
open BstLean.Part268 (cell13092)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13092 (gMinus 13092) (1 - (cell13092 i).lower) ≤ 1 ∧
    energyUpper 13092 (gMinus 13092) (BstLean.Part211.gPlus 13092)
      (finiteEnergy 13092 13092 0.011) (1 - (cell13092 i).lower) ≤
      (cell13092 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨10,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨11,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨12,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨13,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨14,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨15,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨16,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨17,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨18,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨19,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨20,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨21,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨22,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨23,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨24,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨25,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨26,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨27,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨28,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨29,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨30,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨31,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨32,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨33,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨34,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨35,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨36,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨37,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨38,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨39,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨40,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨41,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨42,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨43,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨44,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨45,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨46,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨47,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨48,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨49,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨50,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨51,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13092) (by norm_num)
        (q := 1 - (cell13092 ⟨52,by decide⟩).lower)
        (by norm_num [cell13092]) (by norm_num [cell13092])
      exact ⟨E.1,E.2.trans (by norm_num [cell13092])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13092

/-! Source-cell containment and simple scalar guards at 13092. -/
namespace BstLean.Part269.N13092
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13092)
open BstLean.Part268 (cell13092)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13092 ⟨10,by decide⟩).lower ∧ (cell13092 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13092 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13092 ⟨11,by decide⟩).lower ∧ (cell13092 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13092 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13092 ⟨12,by decide⟩).lower ∧ (cell13092 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13092 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13092 ⟨13,by decide⟩).lower ∧ (cell13092 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13092 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13092 ⟨14,by decide⟩).lower ∧ (cell13092 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13092 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13092 ⟨15,by decide⟩).lower ∧ (cell13092 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13092 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13092 ⟨16,by decide⟩).lower ∧ (cell13092 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13092 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13092 ⟨17,by decide⟩).lower ∧ (cell13092 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13092 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13092 ⟨18,by decide⟩).lower ∧ (cell13092 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13092 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13092 ⟨19,by decide⟩).lower ∧ (cell13092 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13092 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13092 ⟨20,by decide⟩).lower ∧ (cell13092 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13092 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13092 ⟨21,by decide⟩).lower ∧ (cell13092 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13092 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13092 ⟨22,by decide⟩).lower ∧ (cell13092 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13092 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13092 ⟨23,by decide⟩).lower ∧ (cell13092 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13092 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13092 ⟨24,by decide⟩).lower ∧ (cell13092 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13092 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13092 ⟨25,by decide⟩).lower ∧ (cell13092 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13092 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13092 ⟨26,by decide⟩).lower ∧ (cell13092 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13092 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13092 ⟨27,by decide⟩).lower ∧ (cell13092 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13092 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13092 ⟨28,by decide⟩).lower ∧ (cell13092 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13092 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13092 ⟨29,by decide⟩).lower ∧ (cell13092 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13092 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13092 ⟨30,by decide⟩).lower ∧ (cell13092 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13092 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13092 ⟨31,by decide⟩).lower ∧ (cell13092 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13092 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13092 ⟨32,by decide⟩).lower ∧ (cell13092 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13092 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13092 ⟨33,by decide⟩).lower ∧ (cell13092 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13092 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13092 ⟨34,by decide⟩).lower ∧ (cell13092 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13092 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13092 ⟨35,by decide⟩).lower ∧ (cell13092 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13092 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13092 ⟨36,by decide⟩).lower ∧ (cell13092 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13092 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13092 ⟨37,by decide⟩).lower ∧ (cell13092 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13092 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13092 ⟨38,by decide⟩).lower ∧ (cell13092 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13092 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13092 ⟨39,by decide⟩).lower ∧ (cell13092 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13092 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13092 ⟨40,by decide⟩).lower ∧ (cell13092 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13092 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13092 ⟨41,by decide⟩).lower ∧ (cell13092 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13092 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13092 ⟨42,by decide⟩).lower ∧ (cell13092 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13092 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13092 ⟨43,by decide⟩).lower ∧ (cell13092 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13092 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13092 ⟨44,by decide⟩).lower ∧ (cell13092 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13092 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13092 ⟨45,by decide⟩).lower ∧ (cell13092 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13092 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13092 ⟨46,by decide⟩).lower ∧ (cell13092 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13092 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13092 ⟨47,by decide⟩).lower ∧ (cell13092 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13092 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13092 ⟨48,by decide⟩).lower ∧ (cell13092 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13092 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13092 ⟨49,by decide⟩).lower ∧ (cell13092 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13092 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13092 ⟨50,by decide⟩).lower ∧ (cell13092 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13092 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13092 ⟨51,by decide⟩).lower ∧ (cell13092 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13092 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13092 ⟨52,by decide⟩).lower ∧ (cell13092 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13092 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13092 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13092 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13092,cell13092,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13092 i).lower ∧
    (cell13092 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13092 i).upper ≤ (0.532 : ℝ) ∧
    (cell13092 i).centre ≤ (0.1 : ℝ) ∧ (cell13092 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13092 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13092 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13092

/-! The local source numeric instances at 13092 have no network premises. -/
namespace BstLean.Part269.N13092
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13092)
open BstLean.Part268 (cell13092)

noncomputable def sourceNumerics13092 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13092 (cell13092 i)
      scalarRow13092.M scalarRow13092.H scalarRow13092.xi := by
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
    energy_allowance := scalarRow13092.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13092]
    centre_nonneg := (scalarRow13092.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13092])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13092
/-! Actual 13093 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13093
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13093 ≤ (1.035263010065 : ℝ) := by
  have hr : (114.424647694454 : ℝ) ≤ √(13093 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.424647694454 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13093 13093 (11 / 1000) ≤
    (0.008353855031 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13093) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.424647694454 : ℝ) ≤ √(13093 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13093)
  have hdiv : K / √(13093 : ℝ) ≤ K / 114.424647694454 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.424647694454 ≤ (0.008353855031 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13093.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13093 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13093 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13093 := gPlus_lower 13093
end BstLean.Part269.N13093

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13093
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035263010064 : ℝ) ≤ wn 13093 := by
  have hn : √(13093 : ℝ) ≤ 114.424647694455 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13093 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.424647694455 ≤ 2 / √(13093 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244191566 : ℝ) ≤ rhoBar 13093 BstLean.Part154.csC ∧
    rhoBar 13093 BstLean.Part154.csC ≤ 0.000244191944 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035263010064 : ℝ) / (1.295212 * 13093) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035263010065 : ℝ) / (1.29521 * 13093) := by gcongr
      _ ≤ (0.000244191944 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13093 BstLean.Part154.csC) ≤ 0.000976827406 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13093 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13093 BstLean.Part154.csC) (piBar (rhoBar 13093 BstLean.Part154.csC)) ≤ 0.000186515189 ∧
    cc1 (rhoBar 13093 BstLean.Part154.csC) (piBar (rhoBar 13093 BstLean.Part154.csC)) ≤ 0.000118680908 ∧
    cc2 (rhoBar 13093 BstLean.Part154.csC) ≤ 0.000068895243 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13093 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13093 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13093 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13093 BstLean.Part154.csC * nuR (rhoBar 13093 BstLean.Part154.csC)) ≤ 0.000488398796 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244191944 : ℝ) * 0.000976827406 := by gcongr
      _ ≤ (0.000488398796 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13093 BstLean.Part154.csC) * nuR (rhoBar 13093 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000976827406 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13093 BstLean.Part154.csC) * rhoBar 13093 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244191944 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244191944 / 2 + 0.399 * 0.000976827406 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186515189 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488398796 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118680908 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244191944 / 1.414213562 := by gcongr
      _ ≤ (0.000068895243 : ℝ) := by norm_num

end BstLean.Part269.N13093

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13093
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13093 BstLean.Part154.csC) (piBar (rhoBar 13093 BstLean.Part154.csC)) ≤ 1.50233E-7 := by
  have hr0 : 0 ≤ rhoBar 13093 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13093 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13093 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13093 BstLean.Part154.csC) (piBar (rhoBar 13093 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13093 BstLean.Part154.csC) (piBar (rhoBar 13093 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13093 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186515189 : ℝ) ^ 2 + 0.000118680908 ^ 2 + 3 * 0.000068895243 ^ 2 +
        2 * 0.797885 * 0.000186515189 * 0.000118680908 + 2 * 0.000186515189 * 0.000068895243 +
        4 * 0.797885 * 0.000118680908 * 0.000068895243 := by gcongr
    _ ≤ (1.50233E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13093 BstLean.Part154.csC Θ ≤ 0.002547682877 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13093 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13093 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13093 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13093 BstLean.Part154.csC) (piBar (rhoBar 13093 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13093 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035263010065 * 1.50233E-7 / (0.000244191566 : ℝ) := by gcongr
    _ ≤ 0.002547682877 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13093 BstLean.Part154.csC Θ ≤ 0.002825291356 + 0.000643757400 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13093 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13093 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13093 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035263010065 : ℝ) * ((2 * Θ * 0.000244191944 +
        (6863 / 10000) * 0.000244191944 * 13093 * 0.000976827406) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002825291356 + 0.000643757400 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13093 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13093 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13093 0.011 Θ ∧ gammaRatio 13093 0.011 Θ ≤ 0.000083946876 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13093 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035263010065 : ℝ) * 0.525 / ((1 - 0.011) * 13093) := by gcongr
      _ ≤ (0.000083946876 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13093 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13093 0.011 Θ) :=
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
    badAllowance 13093 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13093 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13093 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13093 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13093 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13093 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13093 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13093 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13093 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13093 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13093 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035263010065 : ℝ) * 13093 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13093 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003173543704 + 0.003191440277 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13093

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13093
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13093 BstLean.Part154.csC) (piBar (rhoBar 13093 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13093 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13093 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13093 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13093 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13093 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13093 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13093 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13093 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13093 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13093 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13093 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13093 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13093 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13093 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051682149826 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13093) ≤ 0.010436891047 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13093 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035263010065)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010436891047 + 2 * 0.737676 / 13093) := by gcongr
    _ ≤ (0.051682149826 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13093 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13093

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13093
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520807454 : ℝ) ≤ plow 13093 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13093) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052355649850)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337533511) : eMP 13093 0.011 xi bn ≤ 0.001152006017 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13093 : ℝ) * (1 - 0.011))) ≤ 0.000569651922 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001337533511 / (13093 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569651922 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569651922 : ℝ) + 3.141593 * 0.052355649850 / (13093 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001152006017 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052355649850)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337533511) : PiBarMP 13093 12 0.011 xi bn ≤ 0.158788545367 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13093 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036572305246 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.793571874688 : ℝ) ≤ √((13093 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.424647694454 : ℝ) ≤ √(13093 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13093) ≤ 0.121760551975 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036572305246 + 0.052355649850 * 1.772454 / (2 * (113.793571874688 : ℝ))) * (1 + 0.001152006017) +
        8 / (13093 * 114.424647694454) + 0.121760551975 := by gcongr
    _ ≤ (0.158788545367 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052355649850)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337533511) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280495719900) :
    parallelOracle 13093 0.011 xi bn cd ≤ 0.159749118793 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13093 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13093 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520807454 : ℝ) ≤ plow 13093 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.424647694454 : ℝ) ≤ √(13093 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280495719900 : ℝ) / (2 * 0.560520807454 * 114.424647694454)) * 0.158788545367 +
        0.280495719900 ^ 2 / (2 * 0.560520807454 * 114.424647694454) := by gcongr
    _ ≤ (0.159749118793 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052355649850) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337533511)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280495719900) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13093 13093 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520807454 : ℝ) ≤ plow 13093 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.424647694454 : ℝ) ≤ √(13093 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13093 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13093 Θ 1.22 ≤ 0.011589290654 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.424647694454 := by gcongr <;> linarith
      _ ≤ (0.011589290654 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13093 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13093 13093 0.011 ≤ 0.008353855031 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13093 13093 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13093 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13093 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13093 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13093 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159749118793 + 0.011589290654 + (0.008353855031 : ℝ) *
        (1 + 2 * (0.280495719900 + 0.011589290654) / (0.560520807454 * 114.424647694454))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13093]

end BstLean.Part269.N13093

/-! The original eight local profiles supply actual 13093 moment certificates. -/
namespace BstLean.Part269.N13093
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13093 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13093 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13093 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052355649850 ∧
    0 ≤ bN 13093 BstLean.Part154.csC (groupTheta g) ∧ bN 13093 BstLean.Part154.csC (groupTheta g) ≤ 0.001337533511 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13093 13093 0.011
      (momentAllowance 13093 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13093 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13093 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13093 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13093 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13093 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228813570074 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13093 0.011
      (momentAllowance 13093 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13093 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13093
/-! The actual computed-centre upper energy formula at 13093. -/
namespace BstLean.Part269.N13093
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13093

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13093
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13093)
open BstLean.Part268 (cell13093)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084419978823
  | 2 => 0.085345556513
  | 3 => 0.086266882681
  | 4 => 0.087184813125
  | 5 => 0.088100399136
  | 6 => 0.089014918505
  | 7 => 0.089929909842
  | 8 => 0.090847210291
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13093 13093 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13093 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003177634099 + 0.003195984085 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S29.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13093

/-! Actual upper energy certificates on all 43 source endpoints at 13093. -/
namespace BstLean.Part269.N13093
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13093)
open BstLean.Part268 (cell13093)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13093 (gMinus 13093) (1 - (cell13093 i).lower) ≤ 1 ∧
    energyUpper 13093 (gMinus 13093) (BstLean.Part211.gPlus 13093)
      (finiteEnergy 13093 13093 0.011) (1 - (cell13093 i).lower) ≤
      (cell13093 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨10,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨11,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨12,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨13,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨14,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨15,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨16,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨17,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨18,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨19,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨20,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨21,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨22,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨23,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨24,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨25,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨26,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨27,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨28,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨29,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨30,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨31,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨32,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨33,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨34,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨35,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨36,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨37,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨38,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨39,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨40,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨41,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨42,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨43,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨44,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨45,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨46,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨47,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨48,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨49,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨50,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨51,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13093) (by norm_num)
        (q := 1 - (cell13093 ⟨52,by decide⟩).lower)
        (by norm_num [cell13093]) (by norm_num [cell13093])
      exact ⟨E.1,E.2.trans (by norm_num [cell13093])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13093

/-! Source-cell containment and simple scalar guards at 13093. -/
namespace BstLean.Part269.N13093
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13093)
open BstLean.Part268 (cell13093)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13093 ⟨10,by decide⟩).lower ∧ (cell13093 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13093 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13093 ⟨11,by decide⟩).lower ∧ (cell13093 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13093 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13093 ⟨12,by decide⟩).lower ∧ (cell13093 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13093 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13093 ⟨13,by decide⟩).lower ∧ (cell13093 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13093 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13093 ⟨14,by decide⟩).lower ∧ (cell13093 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13093 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13093 ⟨15,by decide⟩).lower ∧ (cell13093 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13093 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13093 ⟨16,by decide⟩).lower ∧ (cell13093 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13093 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13093 ⟨17,by decide⟩).lower ∧ (cell13093 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13093 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13093 ⟨18,by decide⟩).lower ∧ (cell13093 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13093 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13093 ⟨19,by decide⟩).lower ∧ (cell13093 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13093 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13093 ⟨20,by decide⟩).lower ∧ (cell13093 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13093 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13093 ⟨21,by decide⟩).lower ∧ (cell13093 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13093 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13093 ⟨22,by decide⟩).lower ∧ (cell13093 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13093 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13093 ⟨23,by decide⟩).lower ∧ (cell13093 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13093 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13093 ⟨24,by decide⟩).lower ∧ (cell13093 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13093 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13093 ⟨25,by decide⟩).lower ∧ (cell13093 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13093 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13093 ⟨26,by decide⟩).lower ∧ (cell13093 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13093 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13093 ⟨27,by decide⟩).lower ∧ (cell13093 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13093 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13093 ⟨28,by decide⟩).lower ∧ (cell13093 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13093 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13093 ⟨29,by decide⟩).lower ∧ (cell13093 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13093 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13093 ⟨30,by decide⟩).lower ∧ (cell13093 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13093 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13093 ⟨31,by decide⟩).lower ∧ (cell13093 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13093 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13093 ⟨32,by decide⟩).lower ∧ (cell13093 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13093 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13093 ⟨33,by decide⟩).lower ∧ (cell13093 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13093 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13093 ⟨34,by decide⟩).lower ∧ (cell13093 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13093 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13093 ⟨35,by decide⟩).lower ∧ (cell13093 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13093 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13093 ⟨36,by decide⟩).lower ∧ (cell13093 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13093 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13093 ⟨37,by decide⟩).lower ∧ (cell13093 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13093 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13093 ⟨38,by decide⟩).lower ∧ (cell13093 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13093 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13093 ⟨39,by decide⟩).lower ∧ (cell13093 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13093 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13093 ⟨40,by decide⟩).lower ∧ (cell13093 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13093 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13093 ⟨41,by decide⟩).lower ∧ (cell13093 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13093 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13093 ⟨42,by decide⟩).lower ∧ (cell13093 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13093 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13093 ⟨43,by decide⟩).lower ∧ (cell13093 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13093 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13093 ⟨44,by decide⟩).lower ∧ (cell13093 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13093 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13093 ⟨45,by decide⟩).lower ∧ (cell13093 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13093 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13093 ⟨46,by decide⟩).lower ∧ (cell13093 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13093 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13093 ⟨47,by decide⟩).lower ∧ (cell13093 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13093 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13093 ⟨48,by decide⟩).lower ∧ (cell13093 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13093 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13093 ⟨49,by decide⟩).lower ∧ (cell13093 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13093 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13093 ⟨50,by decide⟩).lower ∧ (cell13093 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13093 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13093 ⟨51,by decide⟩).lower ∧ (cell13093 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13093 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13093 ⟨52,by decide⟩).lower ∧ (cell13093 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13093 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13093 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13093 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13093,cell13093,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13093 i).lower ∧
    (cell13093 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13093 i).upper ≤ (0.532 : ℝ) ∧
    (cell13093 i).centre ≤ (0.1 : ℝ) ∧ (cell13093 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13093 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13093 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13093

/-! The local source numeric instances at 13093 have no network premises. -/
namespace BstLean.Part269.N13093
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13093)
open BstLean.Part268 (cell13093)

noncomputable def sourceNumerics13093 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13093 (cell13093 i)
      scalarRow13093.M scalarRow13093.H scalarRow13093.xi := by
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
    energy_allowance := scalarRow13093.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13093]
    centre_nonneg := (scalarRow13093.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13093])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13093
/-! Actual 13094 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13094
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13094 ≤ (1.035261651841 : ℝ) := by
  have hr : (114.429017298935 : ℝ) ≤ √(13094 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.429017298935 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13094 13094 (11 / 1000) ≤
    (0.008353536027 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13094) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.429017298935 : ℝ) ≤ √(13094 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13094)
  have hdiv : K / √(13094 : ℝ) ≤ K / 114.429017298935 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.429017298935 ≤ (0.008353536027 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13094.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13094 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13094 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13094 := gPlus_lower 13094
end BstLean.Part269.N13094

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13094
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035261651840 : ℝ) ≤ wn 13094 := by
  have hn : √(13094 : ℝ) ≤ 114.429017298936 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13094 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.429017298936 ≤ 2 / √(13094 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244172597 : ℝ) ≤ rhoBar 13094 BstLean.Part154.csC ∧
    rhoBar 13094 BstLean.Part154.csC ≤ 0.000244172975 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035261651840 : ℝ) / (1.295212 * 13094) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035261651841 : ℝ) / (1.29521 * 13094) := by gcongr
      _ ≤ (0.000244172975 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13094 BstLean.Part154.csC) ≤ 0.000976751521 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13094 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13094 BstLean.Part154.csC) (piBar (rhoBar 13094 BstLean.Part154.csC)) ≤ 0.000186500700 ∧
    cc1 (rhoBar 13094 BstLean.Part154.csC) (piBar (rhoBar 13094 BstLean.Part154.csC)) ≤ 0.000118671689 ∧
    cc2 (rhoBar 13094 BstLean.Part154.csC) ≤ 0.000068889891 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13094 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13094 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13094 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13094 BstLean.Part154.csC * nuR (rhoBar 13094 BstLean.Part154.csC)) ≤ 0.000488360856 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244172975 : ℝ) * 0.000976751521 := by gcongr
      _ ≤ (0.000488360856 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13094 BstLean.Part154.csC) * nuR (rhoBar 13094 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000976751521 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13094 BstLean.Part154.csC) * rhoBar 13094 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244172975 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244172975 / 2 + 0.399 * 0.000976751521 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186500700 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488360856 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118671689 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244172975 / 1.414213562 := by gcongr
      _ ≤ (0.000068889891 : ℝ) := by norm_num

end BstLean.Part269.N13094

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13094
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13094 BstLean.Part154.csC) (piBar (rhoBar 13094 BstLean.Part154.csC)) ≤ 1.50209E-7 := by
  have hr0 : 0 ≤ rhoBar 13094 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13094 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13094 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13094 BstLean.Part154.csC) (piBar (rhoBar 13094 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13094 BstLean.Part154.csC) (piBar (rhoBar 13094 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13094 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186500700 : ℝ) ^ 2 + 0.000118671689 ^ 2 + 3 * 0.000068889891 ^ 2 +
        2 * 0.797885 * 0.000186500700 * 0.000118671689 + 2 * 0.000186500700 * 0.000068889891 +
        4 * 0.797885 * 0.000118671689 * 0.000068889891 := by gcongr
    _ ≤ (1.50209E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13094 BstLean.Part154.csC Θ ≤ 0.002547470427 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13094 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13094 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13094 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13094 BstLean.Part154.csC) (piBar (rhoBar 13094 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13094 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035261651841 * 1.50209E-7 / (0.000244172597 : ℝ) := by gcongr
    _ ≤ 0.002547470427 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13094 BstLean.Part154.csC Θ ≤ 0.002825064466 + 0.000643706548 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13094 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13094 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13094 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035261651841 : ℝ) * ((2 * Θ * 0.000244172975 +
        (6863 / 10000) * 0.000244172975 * 13094 * 0.000976751521) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002825064466 + 0.000643706548 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13094 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13094 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13094 0.011 Θ ∧ gammaRatio 13094 0.011 Θ ≤ 0.000083940355 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13094 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035261651841 : ℝ) * 0.525 / ((1 - 0.011) * 13094) := by gcongr
      _ ≤ (0.000083940355 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13094 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13094 0.011 Θ) :=
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
    badAllowance 13094 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13094 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13094 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13094 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13094 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13094 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13094 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13094 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13094 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13094 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13094 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035261651841 : ℝ) * 13094 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13094 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003173316814 + 0.003191176975 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13094

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13094
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13094 BstLean.Part154.csC) (piBar (rhoBar 13094 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13094 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13094 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13094 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13094 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13094 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13094 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13094 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13094 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13094 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13094 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13094 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13094 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13094 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13094 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051680155208 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13094) ≤ 0.010436492503 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13094 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035261651841)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010436492503 + 2 * 0.737676 / 13094) := by gcongr
    _ ≤ (0.051680155208 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13094 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13094

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13094
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520850000 : ℝ) ≤ plow 13094 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13094) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052355284726)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337421975) : eMP 13094 0.011 xi bn ≤ 0.001151913951 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13094 : ℝ) * (1 - 0.011))) ≤ 0.000569606418 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001337421975 / (13094 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569606418 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569606418 : ℝ) + 3.141593 * 0.052355284726 / (13094 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001151913951 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052355284726)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337421975) : PiBarMP 13094 12 0.011 xi bn ≤ 0.158782346690 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13094 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036570780345 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.797917379888 : ℝ) ≤ √((13094 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.429017298935 : ℝ) ≤ √(13094 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13094) ≤ 0.121755902407 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036570780345 + 0.052355284726 * 1.772454 / (2 * (113.797917379888 : ℝ))) * (1 + 0.001151913951) +
        8 / (13094 * 114.429017298935) + 0.121755902407 := by gcongr
    _ ≤ (0.158782346690 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052355284726)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337421975) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280492927418) :
    parallelOracle 13094 0.011 xi bn cd ≤ 0.159742854140 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13094 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13094 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520850000 : ℝ) ≤ plow 13094 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.429017298935 : ℝ) ≤ √(13094 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280492927418 : ℝ) / (2 * 0.560520850000 * 114.429017298935)) * 0.158782346690 +
        0.280492927418 ^ 2 / (2 * 0.560520850000 * 114.429017298935) := by gcongr
    _ ≤ (0.159742854140 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052355284726) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337421975)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280492927418) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13094 13094 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520850000 : ℝ) ≤ plow 13094 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.429017298935 : ℝ) ≤ √(13094 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13094 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13094 Θ 1.22 ≤ 0.011588848103 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.429017298935 := by gcongr <;> linarith
      _ ≤ (0.011588848103 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13094 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13094 13094 0.011 ≤ 0.008353536027 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13094 13094 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13094 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13094 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13094 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13094 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159742854140 + 0.011588848103 + (0.008353536027 : ℝ) *
        (1 + 2 * (0.280492927418 + 0.011588848103) / (0.560520850000 * 114.429017298935))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13094]

end BstLean.Part269.N13094

/-! The original eight local profiles supply actual 13094 moment certificates. -/
namespace BstLean.Part269.N13094
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13094 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13094 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13094 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052355284726 ∧
    0 ≤ bN 13094 BstLean.Part154.csC (groupTheta g) ∧ bN 13094 BstLean.Part154.csC (groupTheta g) ≤ 0.001337421975 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13094 13094 0.011
      (momentAllowance 13094 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13094 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13094 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13094 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13094 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13094 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228812772210 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13094 0.011
      (momentAllowance 13094 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13094 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13094
/-! The actual computed-centre upper energy formula at 13094. -/
namespace BstLean.Part269.N13094
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13094

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13094
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13094)
open BstLean.Part268 (cell13094)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084417432579
  | 2 => 0.085342978221
  | 3 => 0.086264267687
  | 4 => 0.087182155671
  | 5 => 0.088097692154
  | 6 => 0.089012153388
  | 7 => 0.089927076180
  | 8 => 0.090844295579
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13094 13094 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13094 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003177634099 + 0.003195984085 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S29.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13094

/-! Actual upper energy certificates on all 43 source endpoints at 13094. -/
namespace BstLean.Part269.N13094
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13094)
open BstLean.Part268 (cell13094)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13094 (gMinus 13094) (1 - (cell13094 i).lower) ≤ 1 ∧
    energyUpper 13094 (gMinus 13094) (BstLean.Part211.gPlus 13094)
      (finiteEnergy 13094 13094 0.011) (1 - (cell13094 i).lower) ≤
      (cell13094 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨10,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨11,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨12,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨13,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨14,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨15,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨16,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨17,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨18,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨19,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨20,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨21,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨22,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨23,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨24,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨25,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨26,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨27,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨28,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨29,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨30,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨31,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨32,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨33,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨34,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨35,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨36,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨37,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨38,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨39,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨40,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨41,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨42,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨43,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨44,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨45,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨46,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨47,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨48,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨49,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨50,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨51,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13094) (by norm_num)
        (q := 1 - (cell13094 ⟨52,by decide⟩).lower)
        (by norm_num [cell13094]) (by norm_num [cell13094])
      exact ⟨E.1,E.2.trans (by norm_num [cell13094])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13094

/-! Source-cell containment and simple scalar guards at 13094. -/
namespace BstLean.Part269.N13094
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13094)
open BstLean.Part268 (cell13094)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13094 ⟨10,by decide⟩).lower ∧ (cell13094 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13094 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13094 ⟨11,by decide⟩).lower ∧ (cell13094 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13094 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13094 ⟨12,by decide⟩).lower ∧ (cell13094 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13094 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13094 ⟨13,by decide⟩).lower ∧ (cell13094 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13094 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13094 ⟨14,by decide⟩).lower ∧ (cell13094 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13094 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13094 ⟨15,by decide⟩).lower ∧ (cell13094 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13094 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13094 ⟨16,by decide⟩).lower ∧ (cell13094 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13094 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13094 ⟨17,by decide⟩).lower ∧ (cell13094 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13094 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13094 ⟨18,by decide⟩).lower ∧ (cell13094 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13094 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13094 ⟨19,by decide⟩).lower ∧ (cell13094 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13094 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13094 ⟨20,by decide⟩).lower ∧ (cell13094 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13094 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13094 ⟨21,by decide⟩).lower ∧ (cell13094 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13094 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13094 ⟨22,by decide⟩).lower ∧ (cell13094 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13094 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13094 ⟨23,by decide⟩).lower ∧ (cell13094 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13094 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13094 ⟨24,by decide⟩).lower ∧ (cell13094 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13094 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13094 ⟨25,by decide⟩).lower ∧ (cell13094 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13094 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13094 ⟨26,by decide⟩).lower ∧ (cell13094 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13094 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13094 ⟨27,by decide⟩).lower ∧ (cell13094 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13094 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13094 ⟨28,by decide⟩).lower ∧ (cell13094 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13094 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13094 ⟨29,by decide⟩).lower ∧ (cell13094 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13094 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13094 ⟨30,by decide⟩).lower ∧ (cell13094 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13094 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13094 ⟨31,by decide⟩).lower ∧ (cell13094 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13094 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13094 ⟨32,by decide⟩).lower ∧ (cell13094 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13094 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13094 ⟨33,by decide⟩).lower ∧ (cell13094 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13094 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13094 ⟨34,by decide⟩).lower ∧ (cell13094 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13094 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13094 ⟨35,by decide⟩).lower ∧ (cell13094 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13094 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13094 ⟨36,by decide⟩).lower ∧ (cell13094 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13094 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13094 ⟨37,by decide⟩).lower ∧ (cell13094 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13094 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13094 ⟨38,by decide⟩).lower ∧ (cell13094 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13094 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13094 ⟨39,by decide⟩).lower ∧ (cell13094 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13094 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13094 ⟨40,by decide⟩).lower ∧ (cell13094 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13094 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13094 ⟨41,by decide⟩).lower ∧ (cell13094 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13094 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13094 ⟨42,by decide⟩).lower ∧ (cell13094 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13094 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13094 ⟨43,by decide⟩).lower ∧ (cell13094 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13094 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13094 ⟨44,by decide⟩).lower ∧ (cell13094 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13094 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13094 ⟨45,by decide⟩).lower ∧ (cell13094 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13094 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13094 ⟨46,by decide⟩).lower ∧ (cell13094 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13094 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13094 ⟨47,by decide⟩).lower ∧ (cell13094 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13094 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13094 ⟨48,by decide⟩).lower ∧ (cell13094 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13094 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13094 ⟨49,by decide⟩).lower ∧ (cell13094 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13094 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13094 ⟨50,by decide⟩).lower ∧ (cell13094 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13094 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13094 ⟨51,by decide⟩).lower ∧ (cell13094 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13094 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13094 ⟨52,by decide⟩).lower ∧ (cell13094 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13094 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13094 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13094 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13094,cell13094,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13094 i).lower ∧
    (cell13094 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13094 i).upper ≤ (0.532 : ℝ) ∧
    (cell13094 i).centre ≤ (0.1 : ℝ) ∧ (cell13094 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13094 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13094 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13094

/-! The local source numeric instances at 13094 have no network premises. -/
namespace BstLean.Part269.N13094
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13094)
open BstLean.Part268 (cell13094)

noncomputable def sourceNumerics13094 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13094 (cell13094 i)
      scalarRow13094.M scalarRow13094.H scalarRow13094.xi := by
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
    energy_allowance := scalarRow13094.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13094]
    centre_nonneg := (scalarRow13094.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13094])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13094
/-! Actual 13095 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13095
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13095 ≤ (1.035260293773 : ℝ) := by
  have hr : (114.433386736563 : ℝ) ≤ √(13095 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.433386736563 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13095 13095 (11 / 1000) ≤
    (0.008353217060 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13095) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.433386736563 : ℝ) ≤ √(13095 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13095)
  have hdiv : K / √(13095 : ℝ) ≤ K / 114.433386736563 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.433386736563 ≤ (0.008353217060 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13095.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13095 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13095 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13095 := gPlus_lower 13095
end BstLean.Part269.N13095

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13095
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035260293772 : ℝ) ≤ wn 13095 := by
  have hn : √(13095 : ℝ) ≤ 114.433386736564 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13095 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.433386736564 ≤ 2 / √(13095 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244153630 : ℝ) ≤ rhoBar 13095 BstLean.Part154.csC ∧
    rhoBar 13095 BstLean.Part154.csC ≤ 0.000244154008 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035260293772 : ℝ) / (1.295212 * 13095) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035260293773 : ℝ) / (1.29521 * 13095) := by gcongr
      _ ≤ (0.000244154008 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13095 BstLean.Part154.csC) ≤ 0.000976675644 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13095 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13095 BstLean.Part154.csC) (piBar (rhoBar 13095 BstLean.Part154.csC)) ≤ 0.000186486212 ∧
    cc1 (rhoBar 13095 BstLean.Part154.csC) (piBar (rhoBar 13095 BstLean.Part154.csC)) ≤ 0.000118662470 ∧
    cc2 (rhoBar 13095 BstLean.Part154.csC) ≤ 0.000068884539 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13095 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13095 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13095 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13095 BstLean.Part154.csC * nuR (rhoBar 13095 BstLean.Part154.csC)) ≤ 0.000488322919 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244154008 : ℝ) * 0.000976675644 := by gcongr
      _ ≤ (0.000488322919 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13095 BstLean.Part154.csC) * nuR (rhoBar 13095 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000976675644 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13095 BstLean.Part154.csC) * rhoBar 13095 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244154008 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244154008 / 2 + 0.399 * 0.000976675644 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186486212 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488322919 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118662470 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244154008 / 1.414213562 := by gcongr
      _ ≤ (0.000068884539 : ℝ) := by norm_num

end BstLean.Part269.N13095

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13095
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13095 BstLean.Part154.csC) (piBar (rhoBar 13095 BstLean.Part154.csC)) ≤ 1.50186E-7 := by
  have hr0 : 0 ≤ rhoBar 13095 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13095 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13095 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13095 BstLean.Part154.csC) (piBar (rhoBar 13095 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13095 BstLean.Part154.csC) (piBar (rhoBar 13095 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13095 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186486212 : ℝ) ^ 2 + 0.000118662470 ^ 2 + 3 * 0.000068884539 ^ 2 +
        2 * 0.797885 * 0.000186486212 * 0.000118662470 + 2 * 0.000186486212 * 0.000068884539 +
        4 * 0.797885 * 0.000118662470 * 0.000068884539 := by gcongr
    _ ≤ (1.50186E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13095 BstLean.Part154.csC Θ ≤ 0.002547274886 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13095 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13095 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13095 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13095 BstLean.Part154.csC) (piBar (rhoBar 13095 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13095 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035260293773 * 1.50186E-7 / (0.000244153630 : ℝ) := by gcongr
    _ ≤ 0.002547274886 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13095 BstLean.Part154.csC Θ ≤ 0.002824837590 + 0.000643655701 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13095 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13095 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13095 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035260293773 : ℝ) * ((2 * Θ * 0.000244154008 +
        (6863 / 10000) * 0.000244154008 * 13095 * 0.000976675644) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002824837590 + 0.000643655701 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13095 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13095 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13095 0.011 Θ ∧ gammaRatio 13095 0.011 Θ ≤ 0.000083933835 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13095 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035260293773 : ℝ) * 0.525 / ((1 - 0.011) * 13095) := by gcongr
      _ ≤ (0.000083933835 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13095 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13095 0.011 Θ) :=
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
    badAllowance 13095 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13095 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13095 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13095 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13095 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13095 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13095 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13095 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13095 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13095 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13095 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035260293773 : ℝ) * 13095 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13095 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003173089938 + 0.003190930587 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13095

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13095
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13095 BstLean.Part154.csC) (piBar (rhoBar 13095 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13095 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13095 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13095 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13095 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13095 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13095 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13095 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13095 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13095 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13095 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13095 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13095 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13095 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13095 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051678160812 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13095) ≤ 0.010436094003 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13095 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035260293773)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010436094003 + 2 * 0.737676 / 13095) := by gcongr
    _ ≤ (0.051678160812 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13095 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13095

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13095
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520892539 : ℝ) ≤ plow 13095 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13095) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052354928497)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337319316) : eMP 13095 0.011 xi bn ≤ 0.001151825674 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13095 : ℝ) * (1 - 0.011))) ≤ 0.000569562808 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001337319316 / (13095 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569562808 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569562808 : ℝ) + 3.141593 * 0.052354928497 / (13095 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001151825674 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052354928497)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337319316) : PiBarMP 13095 12 0.011 xi bn ≤ 0.158776270206 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13095 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036569376752 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.802262719156 : ℝ) ≤ √((13095 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.433386736563 : ℝ) ≤ √(13095 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13095) ≤ 0.121751253372 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036569376752 + 0.052354928497 * 1.772454 / (2 * (113.802262719156 : ℝ))) * (1 + 0.001151825674) +
        8 / (13095 * 114.433386736563) + 0.121751253372 := by gcongr
    _ ≤ (0.158776270206 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052354928497)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337319316) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280490154591) :
    parallelOracle 13095 0.011 xi bn cd ≤ 0.159736712065 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13095 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13095 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520892539 : ℝ) ≤ plow 13095 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.433386736563 : ℝ) ≤ √(13095 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280490154591 : ℝ) / (2 * 0.560520892539 * 114.433386736563)) * 0.158776270206 +
        0.280490154591 ^ 2 / (2 * 0.560520892539 * 114.433386736563) := by gcongr
    _ ≤ (0.159736712065 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052354928497) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337319316)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280490154591) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13095 13095 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520892539 : ℝ) ≤ plow 13095 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.433386736563 : ℝ) ≤ √(13095 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13095 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13095 Θ 1.22 ≤ 0.011588405603 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.433386736563 := by gcongr <;> linarith
      _ ≤ (0.011588405603 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13095 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13095 13095 0.011 ≤ 0.008353217060 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13095 13095 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13095 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13095 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13095 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13095 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159736712065 + 0.011588405603 + (0.008353217060 : ℝ) *
        (1 + 2 * (0.280490154591 + 0.011588405603) / (0.560520892539 * 114.433386736563))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13095]

end BstLean.Part269.N13095

/-! The original eight local profiles supply actual 13095 moment certificates. -/
namespace BstLean.Part269.N13095
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13095 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13095 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13095 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052354928497 ∧
    0 ≤ bN 13095 BstLean.Part154.csC (groupTheta g) ∧ bN 13095 BstLean.Part154.csC (groupTheta g) ≤ 0.001337319316 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13095 13095 0.011
      (momentAllowance 13095 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13095 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13095 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13095 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13095 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13095 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228811993779 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13095 0.011
      (momentAllowance 13095 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13095 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13095
/-! The actual computed-centre upper energy formula at 13095. -/
namespace BstLean.Part269.N13095
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13095

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13095
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13095)
open BstLean.Part268 (cell13095)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084414887076
  | 2 => 0.085340400695
  | 3 => 0.086261653490
  | 4 => 0.087179499054
  | 5 => 0.088094986057
  | 6 => 0.089009389213
  | 7 => 0.089924243530
  | 8 => 0.090841381966
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13095 13095 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13095 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003177634099 + 0.003195984085 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S29.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13095

/-! Actual upper energy certificates on all 43 source endpoints at 13095. -/
namespace BstLean.Part269.N13095
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13095)
open BstLean.Part268 (cell13095)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13095 (gMinus 13095) (1 - (cell13095 i).lower) ≤ 1 ∧
    energyUpper 13095 (gMinus 13095) (BstLean.Part211.gPlus 13095)
      (finiteEnergy 13095 13095 0.011) (1 - (cell13095 i).lower) ≤
      (cell13095 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨10,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨11,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨12,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨13,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨14,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨15,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨16,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨17,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨18,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨19,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨20,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨21,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨22,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨23,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨24,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨25,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨26,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨27,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨28,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨29,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨30,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨31,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨32,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨33,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨34,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨35,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨36,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨37,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨38,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨39,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨40,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨41,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨42,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨43,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨44,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨45,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨46,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨47,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨48,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨49,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨50,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨51,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13095) (by norm_num)
        (q := 1 - (cell13095 ⟨52,by decide⟩).lower)
        (by norm_num [cell13095]) (by norm_num [cell13095])
      exact ⟨E.1,E.2.trans (by norm_num [cell13095])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13095

/-! Source-cell containment and simple scalar guards at 13095. -/
namespace BstLean.Part269.N13095
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13095)
open BstLean.Part268 (cell13095)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13095 ⟨10,by decide⟩).lower ∧ (cell13095 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13095 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13095 ⟨11,by decide⟩).lower ∧ (cell13095 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13095 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13095 ⟨12,by decide⟩).lower ∧ (cell13095 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13095 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13095 ⟨13,by decide⟩).lower ∧ (cell13095 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13095 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13095 ⟨14,by decide⟩).lower ∧ (cell13095 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13095 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13095 ⟨15,by decide⟩).lower ∧ (cell13095 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13095 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13095 ⟨16,by decide⟩).lower ∧ (cell13095 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13095 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13095 ⟨17,by decide⟩).lower ∧ (cell13095 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13095 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13095 ⟨18,by decide⟩).lower ∧ (cell13095 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13095 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13095 ⟨19,by decide⟩).lower ∧ (cell13095 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13095 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13095 ⟨20,by decide⟩).lower ∧ (cell13095 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13095 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13095 ⟨21,by decide⟩).lower ∧ (cell13095 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13095 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13095 ⟨22,by decide⟩).lower ∧ (cell13095 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13095 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13095 ⟨23,by decide⟩).lower ∧ (cell13095 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13095 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13095 ⟨24,by decide⟩).lower ∧ (cell13095 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13095 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13095 ⟨25,by decide⟩).lower ∧ (cell13095 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13095 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13095 ⟨26,by decide⟩).lower ∧ (cell13095 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13095 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13095 ⟨27,by decide⟩).lower ∧ (cell13095 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13095 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13095 ⟨28,by decide⟩).lower ∧ (cell13095 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13095 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13095 ⟨29,by decide⟩).lower ∧ (cell13095 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13095 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13095 ⟨30,by decide⟩).lower ∧ (cell13095 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13095 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13095 ⟨31,by decide⟩).lower ∧ (cell13095 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13095 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13095 ⟨32,by decide⟩).lower ∧ (cell13095 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13095 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13095 ⟨33,by decide⟩).lower ∧ (cell13095 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13095 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13095 ⟨34,by decide⟩).lower ∧ (cell13095 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13095 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13095 ⟨35,by decide⟩).lower ∧ (cell13095 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13095 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13095 ⟨36,by decide⟩).lower ∧ (cell13095 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13095 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13095 ⟨37,by decide⟩).lower ∧ (cell13095 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13095 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13095 ⟨38,by decide⟩).lower ∧ (cell13095 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13095 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13095 ⟨39,by decide⟩).lower ∧ (cell13095 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13095 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13095 ⟨40,by decide⟩).lower ∧ (cell13095 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13095 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13095 ⟨41,by decide⟩).lower ∧ (cell13095 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13095 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13095 ⟨42,by decide⟩).lower ∧ (cell13095 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13095 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13095 ⟨43,by decide⟩).lower ∧ (cell13095 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13095 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13095 ⟨44,by decide⟩).lower ∧ (cell13095 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13095 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13095 ⟨45,by decide⟩).lower ∧ (cell13095 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13095 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13095 ⟨46,by decide⟩).lower ∧ (cell13095 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13095 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13095 ⟨47,by decide⟩).lower ∧ (cell13095 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13095 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13095 ⟨48,by decide⟩).lower ∧ (cell13095 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13095 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13095 ⟨49,by decide⟩).lower ∧ (cell13095 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13095 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13095 ⟨50,by decide⟩).lower ∧ (cell13095 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13095 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13095 ⟨51,by decide⟩).lower ∧ (cell13095 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13095 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13095 ⟨52,by decide⟩).lower ∧ (cell13095 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13095 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13095 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13095 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13095,cell13095,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13095 i).lower ∧
    (cell13095 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13095 i).upper ≤ (0.532 : ℝ) ∧
    (cell13095 i).centre ≤ (0.1 : ℝ) ∧ (cell13095 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13095 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13095 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13095

/-! The local source numeric instances at 13095 have no network premises. -/
namespace BstLean.Part269.N13095
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13095)
open BstLean.Part268 (cell13095)

noncomputable def sourceNumerics13095 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13095 (cell13095 i)
      scalarRow13095.M scalarRow13095.H scalarRow13095.xi := by
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
    energy_allowance := scalarRow13095.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13095]
    centre_nonneg := (scalarRow13095.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13095])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13095
/-! Actual 13096 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13096
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13096 ≤ (1.035258935861 : ℝ) := by
  have hr : (114.437756007359 : ℝ) ≤ √(13096 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.437756007359 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13096 13096 (11 / 1000) ≤
    (0.008352898129 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13096) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.437756007359 : ℝ) ≤ √(13096 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13096)
  have hdiv : K / √(13096 : ℝ) ≤ K / 114.437756007359 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.437756007359 ≤ (0.008352898129 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13096.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13096 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13096 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13096 := gPlus_lower 13096
end BstLean.Part269.N13096

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13096
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035258935860 : ℝ) ≤ wn 13096 := by
  have hn : √(13096 : ℝ) ≤ 114.437756007360 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13096 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.437756007360 ≤ 2 / √(13096 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244134666 : ℝ) ≤ rhoBar 13096 BstLean.Part154.csC ∧
    rhoBar 13096 BstLean.Part154.csC ≤ 0.000244135044 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035258935860 : ℝ) / (1.295212 * 13096) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035258935861 : ℝ) / (1.29521 * 13096) := by gcongr
      _ ≤ (0.000244135044 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13096 BstLean.Part154.csC) ≤ 0.000976599778 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13096 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13096 BstLean.Part154.csC) (piBar (rhoBar 13096 BstLean.Part154.csC)) ≤ 0.000186471727 ∧
    cc1 (rhoBar 13096 BstLean.Part154.csC) (piBar (rhoBar 13096 BstLean.Part154.csC)) ≤ 0.000118653253 ∧
    cc2 (rhoBar 13096 BstLean.Part154.csC) ≤ 0.000068879189 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13096 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13096 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13096 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13096 BstLean.Part154.csC * nuR (rhoBar 13096 BstLean.Part154.csC)) ≤ 0.000488284989 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244135044 : ℝ) * 0.000976599778 := by gcongr
      _ ≤ (0.000488284989 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13096 BstLean.Part154.csC) * nuR (rhoBar 13096 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000976599778 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13096 BstLean.Part154.csC) * rhoBar 13096 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244135044 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244135044 / 2 + 0.399 * 0.000976599778 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186471727 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488284989 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118653253 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244135044 / 1.414213562 := by gcongr
      _ ≤ (0.000068879189 : ℝ) := by norm_num

end BstLean.Part269.N13096

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13096
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13096 BstLean.Part154.csC) (piBar (rhoBar 13096 BstLean.Part154.csC)) ≤ 1.50163E-7 := by
  have hr0 : 0 ≤ rhoBar 13096 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13096 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13096 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13096 BstLean.Part154.csC) (piBar (rhoBar 13096 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13096 BstLean.Part154.csC) (piBar (rhoBar 13096 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13096 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186471727 : ℝ) ^ 2 + 0.000118653253 ^ 2 + 3 * 0.000068879189 ^ 2 +
        2 * 0.797885 * 0.000186471727 * 0.000118653253 + 2 * 0.000186471727 * 0.000068879189 +
        4 * 0.797885 * 0.000118653253 * 0.000068879189 := by gcongr
    _ ≤ (1.50163E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13096 BstLean.Part154.csC Θ ≤ 0.002547079285 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13096 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13096 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13096 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13096 BstLean.Part154.csC) (piBar (rhoBar 13096 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13096 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035258935861 * 1.50163E-7 / (0.000244134666 : ℝ) := by gcongr
    _ ≤ 0.002547079285 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13096 BstLean.Part154.csC Θ ≤ 0.002824610749 + 0.000643604863 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13096 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13096 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13096 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035258935861 : ℝ) * ((2 * Θ * 0.000244135044 +
        (6863 / 10000) * 0.000244135044 * 13096 * 0.000976599778) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002824610749 + 0.000643604863 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13096 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13096 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13096 0.011 Θ ∧ gammaRatio 13096 0.011 Θ ≤ 0.000083927315 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13096 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035258935861 : ℝ) * 0.525 / ((1 - 0.011) * 13096) := by gcongr
      _ ≤ (0.000083927315 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13096 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13096 0.011 Θ) :=
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
    badAllowance 13096 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13096 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13096 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13096 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13096 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13096 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13096 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13096 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13096 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13096 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13096 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035258935861 : ℝ) * 13096 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13096 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003172863097 + 0.003190684148 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13096

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13096
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13096 BstLean.Part154.csC) (piBar (rhoBar 13096 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13096 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13096 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13096 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13096 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13096 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13096 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13096 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13096 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13096 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13096 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13096 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13096 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13096 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13096 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051676166653 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13096) ≤ 0.010435695550 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13096 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035258935861)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010435695550 + 2 * 0.737676 / 13096) := by gcongr
    _ ≤ (0.051676166653 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13096 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13096

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13096
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520935071 : ℝ) ≤ plow 13096 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13096) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052354572275)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337216625) : eMP 13096 0.011 xi bn ≤ 0.001151737390 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13096 : ℝ) * (1 - 0.011))) ≤ 0.000569519194 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001337216625 / (13096 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569519194 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569519194 : ℝ) + 3.141593 * 0.052354572275 / (13096 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001151737390 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052354572275)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337216625) : PiBarMP 13096 12 0.011 xi bn ≤ 0.158770193765 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13096 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036567972668 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.806607892512 : ℝ) ≤ √((13096 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.437756007359 : ℝ) ≤ √(13096 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13096) ≤ 0.121746604870 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036567972668 + 0.052354572275 * 1.772454 / (2 * (113.806607892512 : ℝ))) * (1 + 0.001151737390) +
        8 / (13096 * 114.437756007359) + 0.121746604870 := by gcongr
    _ ≤ (0.158770193765 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052354572275)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337216625) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280487382015) :
    parallelOracle 13096 0.011 xi bn cd ≤ 0.159730570040 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13096 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13096 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520935071 : ℝ) ≤ plow 13096 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.437756007359 : ℝ) ≤ √(13096 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280487382015 : ℝ) / (2 * 0.560520935071 * 114.437756007359)) * 0.158770193765 +
        0.280487382015 ^ 2 / (2 * 0.560520935071 * 114.437756007359) := by gcongr
    _ ≤ (0.159730570040 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052354572275) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337216625)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280487382015) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13096 13096 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520935071 : ℝ) ≤ plow 13096 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.437756007359 : ℝ) ≤ √(13096 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13096 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13096 Θ 1.22 ≤ 0.011587963154 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.437756007359 := by gcongr <;> linarith
      _ ≤ (0.011587963154 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13096 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13096 13096 0.011 ≤ 0.008352898129 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13096 13096 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13096 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13096 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13096 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13096 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159730570040 + 0.011587963154 + (0.008352898129 : ℝ) *
        (1 + 2 * (0.280487382015 + 0.011587963154) / (0.560520935071 * 114.437756007359))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13096]

end BstLean.Part269.N13096

/-! The original eight local profiles supply actual 13096 moment certificates. -/
namespace BstLean.Part269.N13096
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13096 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13096 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13096 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052354572275 ∧
    0 ≤ bN 13096 BstLean.Part154.csC (groupTheta g) ∧ bN 13096 BstLean.Part154.csC (groupTheta g) ≤ 0.001337216625 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13096 13096 0.011
      (momentAllowance 13096 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13096 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13096 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13096 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13096 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13096 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228811215362 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13096 0.011
      (momentAllowance 13096 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13096 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13096
/-! The actual computed-centre upper energy formula at 13096. -/
namespace BstLean.Part269.N13096
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13096

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13096
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13096)
open BstLean.Part268 (cell13096)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084412342314
  | 2 => 0.085337823935
  | 3 => 0.086259040092
  | 4 => 0.087176843272
  | 5 => 0.088092280843
  | 6 => 0.089006625981
  | 7 => 0.089921411894
  | 8 => 0.090838469451
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13096 13096 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13096 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003177634099 + 0.003195984085 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S29.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13096

/-! Actual upper energy certificates on all 43 source endpoints at 13096. -/
namespace BstLean.Part269.N13096
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13096)
open BstLean.Part268 (cell13096)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13096 (gMinus 13096) (1 - (cell13096 i).lower) ≤ 1 ∧
    energyUpper 13096 (gMinus 13096) (BstLean.Part211.gPlus 13096)
      (finiteEnergy 13096 13096 0.011) (1 - (cell13096 i).lower) ≤
      (cell13096 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨10,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨11,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨12,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨13,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨14,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨15,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨16,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨17,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨18,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨19,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨20,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨21,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨22,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨23,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨24,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨25,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨26,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨27,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨28,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨29,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨30,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨31,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨32,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨33,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨34,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨35,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨36,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨37,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨38,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨39,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨40,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨41,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨42,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨43,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨44,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨45,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨46,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨47,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨48,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨49,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨50,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨51,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13096) (by norm_num)
        (q := 1 - (cell13096 ⟨52,by decide⟩).lower)
        (by norm_num [cell13096]) (by norm_num [cell13096])
      exact ⟨E.1,E.2.trans (by norm_num [cell13096])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13096

/-! Source-cell containment and simple scalar guards at 13096. -/
namespace BstLean.Part269.N13096
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13096)
open BstLean.Part268 (cell13096)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13096 ⟨10,by decide⟩).lower ∧ (cell13096 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13096 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13096 ⟨11,by decide⟩).lower ∧ (cell13096 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13096 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13096 ⟨12,by decide⟩).lower ∧ (cell13096 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13096 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13096 ⟨13,by decide⟩).lower ∧ (cell13096 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13096 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13096 ⟨14,by decide⟩).lower ∧ (cell13096 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13096 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13096 ⟨15,by decide⟩).lower ∧ (cell13096 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13096 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13096 ⟨16,by decide⟩).lower ∧ (cell13096 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13096 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13096 ⟨17,by decide⟩).lower ∧ (cell13096 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13096 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13096 ⟨18,by decide⟩).lower ∧ (cell13096 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13096 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13096 ⟨19,by decide⟩).lower ∧ (cell13096 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13096 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13096 ⟨20,by decide⟩).lower ∧ (cell13096 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13096 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13096 ⟨21,by decide⟩).lower ∧ (cell13096 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13096 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13096 ⟨22,by decide⟩).lower ∧ (cell13096 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13096 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13096 ⟨23,by decide⟩).lower ∧ (cell13096 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13096 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13096 ⟨24,by decide⟩).lower ∧ (cell13096 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13096 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13096 ⟨25,by decide⟩).lower ∧ (cell13096 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13096 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13096 ⟨26,by decide⟩).lower ∧ (cell13096 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13096 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13096 ⟨27,by decide⟩).lower ∧ (cell13096 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13096 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13096 ⟨28,by decide⟩).lower ∧ (cell13096 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13096 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13096 ⟨29,by decide⟩).lower ∧ (cell13096 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13096 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13096 ⟨30,by decide⟩).lower ∧ (cell13096 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13096 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13096 ⟨31,by decide⟩).lower ∧ (cell13096 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13096 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13096 ⟨32,by decide⟩).lower ∧ (cell13096 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13096 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13096 ⟨33,by decide⟩).lower ∧ (cell13096 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13096 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13096 ⟨34,by decide⟩).lower ∧ (cell13096 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13096 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13096 ⟨35,by decide⟩).lower ∧ (cell13096 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13096 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13096 ⟨36,by decide⟩).lower ∧ (cell13096 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13096 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13096 ⟨37,by decide⟩).lower ∧ (cell13096 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13096 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13096 ⟨38,by decide⟩).lower ∧ (cell13096 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13096 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13096 ⟨39,by decide⟩).lower ∧ (cell13096 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13096 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13096 ⟨40,by decide⟩).lower ∧ (cell13096 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13096 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13096 ⟨41,by decide⟩).lower ∧ (cell13096 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13096 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13096 ⟨42,by decide⟩).lower ∧ (cell13096 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13096 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13096 ⟨43,by decide⟩).lower ∧ (cell13096 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13096 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13096 ⟨44,by decide⟩).lower ∧ (cell13096 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13096 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13096 ⟨45,by decide⟩).lower ∧ (cell13096 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13096 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13096 ⟨46,by decide⟩).lower ∧ (cell13096 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13096 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13096 ⟨47,by decide⟩).lower ∧ (cell13096 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13096 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13096 ⟨48,by decide⟩).lower ∧ (cell13096 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13096 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13096 ⟨49,by decide⟩).lower ∧ (cell13096 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13096 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13096 ⟨50,by decide⟩).lower ∧ (cell13096 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13096 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13096 ⟨51,by decide⟩).lower ∧ (cell13096 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13096 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13096 ⟨52,by decide⟩).lower ∧ (cell13096 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13096 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13096 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13096 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13096,cell13096,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13096 i).lower ∧
    (cell13096 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13096 i).upper ≤ (0.532 : ℝ) ∧
    (cell13096 i).centre ≤ (0.1 : ℝ) ∧ (cell13096 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13096 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13096 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13096

/-! The local source numeric instances at 13096 have no network premises. -/
namespace BstLean.Part269.N13096
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13096)
open BstLean.Part268 (cell13096)

noncomputable def sourceNumerics13096 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13096 (cell13096 i)
      scalarRow13096.M scalarRow13096.H scalarRow13096.xi := by
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
    energy_allowance := scalarRow13096.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13096]
    centre_nonneg := (scalarRow13096.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13096])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13096
/-! Actual 13097 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13097
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13097 ≤ (1.035257578106 : ℝ) := by
  have hr : (114.442125111341 : ℝ) ≤ √(13097 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.442125111341 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13097 13097 (11 / 1000) ≤
    (0.008352579234 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13097) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.442125111341 : ℝ) ≤ √(13097 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13097)
  have hdiv : K / √(13097 : ℝ) ≤ K / 114.442125111341 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.442125111341 ≤ (0.008352579234 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13097.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13097 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13097 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13097 := gPlus_lower 13097
end BstLean.Part269.N13097

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13097
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035257578105 : ℝ) ≤ wn 13097 := by
  have hn : √(13097 : ℝ) ≤ 114.442125111342 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13097 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.442125111342 ≤ 2 / √(13097 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244115706 : ℝ) ≤ rhoBar 13097 BstLean.Part154.csC ∧
    rhoBar 13097 BstLean.Part154.csC ≤ 0.000244116084 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035257578105 : ℝ) / (1.295212 * 13097) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035257578106 : ℝ) / (1.29521 * 13097) := by gcongr
      _ ≤ (0.000244116084 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13097 BstLean.Part154.csC) ≤ 0.000976523929 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13097 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13097 BstLean.Part154.csC) (piBar (rhoBar 13097 BstLean.Part154.csC)) ≤ 0.000186457244 ∧
    cc1 (rhoBar 13097 BstLean.Part154.csC) (piBar (rhoBar 13097 BstLean.Part154.csC)) ≤ 0.000118644038 ∧
    cc2 (rhoBar 13097 BstLean.Part154.csC) ≤ 0.000068873840 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13097 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13097 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13097 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13097 BstLean.Part154.csC * nuR (rhoBar 13097 BstLean.Part154.csC)) ≤ 0.000488247067 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244116084 : ℝ) * 0.000976523929 := by gcongr
      _ ≤ (0.000488247067 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13097 BstLean.Part154.csC) * nuR (rhoBar 13097 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000976523929 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13097 BstLean.Part154.csC) * rhoBar 13097 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244116084 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244116084 / 2 + 0.399 * 0.000976523929 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186457244 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488247067 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118644038 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244116084 / 1.414213562 := by gcongr
      _ ≤ (0.000068873840 : ℝ) := by norm_num

end BstLean.Part269.N13097

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13097
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13097 BstLean.Part154.csC) (piBar (rhoBar 13097 BstLean.Part154.csC)) ≤ 1.50139E-7 := by
  have hr0 : 0 ≤ rhoBar 13097 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13097 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13097 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13097 BstLean.Part154.csC) (piBar (rhoBar 13097 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13097 BstLean.Part154.csC) (piBar (rhoBar 13097 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13097 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186457244 : ℝ) ^ 2 + 0.000118644038 ^ 2 + 3 * 0.000068873840 ^ 2 +
        2 * 0.797885 * 0.000186457244 * 0.000118644038 + 2 * 0.000186457244 * 0.000068873840 +
        4 * 0.797885 * 0.000118644038 * 0.000068873840 := by gcongr
    _ ≤ (1.50139E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13097 BstLean.Part154.csC Θ ≤ 0.002546866649 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13097 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13097 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13097 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13097 BstLean.Part154.csC) (piBar (rhoBar 13097 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13097 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035257578106 * 1.50139E-7 / (0.000244115706 : ℝ) := by gcongr
    _ ≤ 0.002546866649 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13097 BstLean.Part154.csC Θ ≤ 0.002824383971 + 0.000643554035 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13097 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13097 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13097 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035257578106 : ℝ) * ((2 * Θ * 0.000244116084 +
        (6863 / 10000) * 0.000244116084 * 13097 * 0.000976523929) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002824383971 + 0.000643554035 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13097 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13097 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13097 0.011 Θ ∧ gammaRatio 13097 0.011 Θ ≤ 0.000083920797 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13097 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035257578106 : ℝ) * 0.525 / ((1 - 0.011) * 13097) := by gcongr
      _ ≤ (0.000083920797 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13097 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13097 0.011 Θ) :=
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
    badAllowance 13097 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13097 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13097 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13097 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13097 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13097 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13097 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13097 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13097 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13097 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13097 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035257578106 : ℝ) * 13097 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13097 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003172636319 + 0.003190420684 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13097

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13097
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13097 BstLean.Part154.csC) (piBar (rhoBar 13097 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13097 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13097 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13097 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13097 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13097 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13097 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13097 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13097 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13097 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13097 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13097 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13097 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13097 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13097 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051674172720 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13097) ≤ 0.010435297142 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13097 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035257578106)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010435297142 + 2 * 0.737676 / 13097) := by gcongr
    _ ≤ (0.051674172720 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13097 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13097

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13097
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520977597 : ℝ) ≤ plow 13097 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13097) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052354207179)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337104991) : eMP 13097 0.011 xi bn ≤ 0.001151645302 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13097 : ℝ) * (1 - 0.011))) ≤ 0.000569473679 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001337104991 / (13097 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569473679 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569473679 : ℝ) + 3.141593 * 0.052354207179 / (13097 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001151645302 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052354207179)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337104991) : PiBarMP 13097 12 0.011 xi bn ≤ 0.158763995170 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13097 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036566446246 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.810952899973 : ℝ) ≤ √((13097 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.442125111341 : ℝ) ≤ √(13097 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13097) ≤ 0.121741956900 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036566446246 + 0.052354207179 * 1.772454 / (2 * (113.810952899973 : ℝ))) * (1 + 0.001151645302) +
        8 / (13097 * 114.442125111341) + 0.121741956900 := by gcongr
    _ ≤ (0.158763995170 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052354207179)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337104991) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280484590270) :
    parallelOracle 13097 0.011 xi bn cd ≤ 0.159724305494 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13097 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13097 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520977597 : ℝ) ≤ plow 13097 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.442125111341 : ℝ) ≤ √(13097 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280484590270 : ℝ) / (2 * 0.560520977597 * 114.442125111341)) * 0.158763995170 +
        0.280484590270 ^ 2 / (2 * 0.560520977597 * 114.442125111341) := by gcongr
    _ ≤ (0.159724305494 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052354207179) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337104991)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280484590270) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13097 13097 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520977597 : ℝ) ≤ plow 13097 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.442125111341 : ℝ) ≤ √(13097 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13097 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13097 Θ 1.22 ≤ 0.011587520756 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.442125111341 := by gcongr <;> linarith
      _ ≤ (0.011587520756 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13097 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13097 13097 0.011 ≤ 0.008352579234 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13097 13097 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13097 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13097 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13097 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13097 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159724305494 + 0.011587520756 + (0.008352579234 : ℝ) *
        (1 + 2 * (0.280484590270 + 0.011587520756) / (0.560520977597 * 114.442125111341))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13097]

end BstLean.Part269.N13097

/-! The original eight local profiles supply actual 13097 moment certificates. -/
namespace BstLean.Part269.N13097
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13097 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13097 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13097 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052354207179 ∧
    0 ≤ bN 13097 BstLean.Part154.csC (groupTheta g) ∧ bN 13097 BstLean.Part154.csC (groupTheta g) ≤ 0.001337104991 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13097 13097 0.011
      (momentAllowance 13097 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13097 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13097 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13097 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13097 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13097 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228810417550 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13097 0.011
      (momentAllowance 13097 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13097 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13097
/-! The actual computed-centre upper energy formula at 13097. -/
namespace BstLean.Part269.N13097
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13097

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13097
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13097)
open BstLean.Part268 (cell13097)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084409798292
  | 2 => 0.085335247940
  | 3 => 0.086256427489
  | 4 => 0.087174188326
  | 5 => 0.088089576513
  | 6 => 0.089003863689
  | 7 => 0.089918581269
  | 8 => 0.090835558032
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13097 13097 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13097 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003177634099 + 0.003195984085 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S29.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13097

/-! Actual upper energy certificates on all 43 source endpoints at 13097. -/
namespace BstLean.Part269.N13097
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13097)
open BstLean.Part268 (cell13097)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13097 (gMinus 13097) (1 - (cell13097 i).lower) ≤ 1 ∧
    energyUpper 13097 (gMinus 13097) (BstLean.Part211.gPlus 13097)
      (finiteEnergy 13097 13097 0.011) (1 - (cell13097 i).lower) ≤
      (cell13097 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨10,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨11,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨12,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨13,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨14,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨15,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨16,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨17,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨18,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨19,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨20,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨21,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨22,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨23,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨24,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨25,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨26,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨27,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨28,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨29,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨30,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨31,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨32,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨33,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨34,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨35,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨36,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨37,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨38,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨39,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨40,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨41,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨42,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨43,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨44,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨45,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨46,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨47,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨48,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨49,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨50,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨51,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13097) (by norm_num)
        (q := 1 - (cell13097 ⟨52,by decide⟩).lower)
        (by norm_num [cell13097]) (by norm_num [cell13097])
      exact ⟨E.1,E.2.trans (by norm_num [cell13097])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13097

/-! Source-cell containment and simple scalar guards at 13097. -/
namespace BstLean.Part269.N13097
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13097)
open BstLean.Part268 (cell13097)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13097 ⟨10,by decide⟩).lower ∧ (cell13097 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13097 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13097 ⟨11,by decide⟩).lower ∧ (cell13097 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13097 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13097 ⟨12,by decide⟩).lower ∧ (cell13097 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13097 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13097 ⟨13,by decide⟩).lower ∧ (cell13097 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13097 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13097 ⟨14,by decide⟩).lower ∧ (cell13097 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13097 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13097 ⟨15,by decide⟩).lower ∧ (cell13097 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13097 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13097 ⟨16,by decide⟩).lower ∧ (cell13097 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13097 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13097 ⟨17,by decide⟩).lower ∧ (cell13097 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13097 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13097 ⟨18,by decide⟩).lower ∧ (cell13097 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13097 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13097 ⟨19,by decide⟩).lower ∧ (cell13097 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13097 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13097 ⟨20,by decide⟩).lower ∧ (cell13097 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13097 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13097 ⟨21,by decide⟩).lower ∧ (cell13097 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13097 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13097 ⟨22,by decide⟩).lower ∧ (cell13097 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13097 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13097 ⟨23,by decide⟩).lower ∧ (cell13097 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13097 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13097 ⟨24,by decide⟩).lower ∧ (cell13097 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13097 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13097 ⟨25,by decide⟩).lower ∧ (cell13097 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13097 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13097 ⟨26,by decide⟩).lower ∧ (cell13097 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13097 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13097 ⟨27,by decide⟩).lower ∧ (cell13097 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13097 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13097 ⟨28,by decide⟩).lower ∧ (cell13097 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13097 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13097 ⟨29,by decide⟩).lower ∧ (cell13097 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13097 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13097 ⟨30,by decide⟩).lower ∧ (cell13097 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13097 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13097 ⟨31,by decide⟩).lower ∧ (cell13097 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13097 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13097 ⟨32,by decide⟩).lower ∧ (cell13097 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13097 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13097 ⟨33,by decide⟩).lower ∧ (cell13097 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13097 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13097 ⟨34,by decide⟩).lower ∧ (cell13097 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13097 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13097 ⟨35,by decide⟩).lower ∧ (cell13097 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13097 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13097 ⟨36,by decide⟩).lower ∧ (cell13097 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13097 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13097 ⟨37,by decide⟩).lower ∧ (cell13097 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13097 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13097 ⟨38,by decide⟩).lower ∧ (cell13097 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13097 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13097 ⟨39,by decide⟩).lower ∧ (cell13097 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13097 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13097 ⟨40,by decide⟩).lower ∧ (cell13097 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13097 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13097 ⟨41,by decide⟩).lower ∧ (cell13097 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13097 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13097 ⟨42,by decide⟩).lower ∧ (cell13097 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13097 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13097 ⟨43,by decide⟩).lower ∧ (cell13097 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13097 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13097 ⟨44,by decide⟩).lower ∧ (cell13097 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13097 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13097 ⟨45,by decide⟩).lower ∧ (cell13097 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13097 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13097 ⟨46,by decide⟩).lower ∧ (cell13097 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13097 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13097 ⟨47,by decide⟩).lower ∧ (cell13097 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13097 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13097 ⟨48,by decide⟩).lower ∧ (cell13097 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13097 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13097 ⟨49,by decide⟩).lower ∧ (cell13097 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13097 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13097 ⟨50,by decide⟩).lower ∧ (cell13097 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13097 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13097 ⟨51,by decide⟩).lower ∧ (cell13097 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13097 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13097 ⟨52,by decide⟩).lower ∧ (cell13097 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13097 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13097 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13097 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13097,cell13097,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13097 i).lower ∧
    (cell13097 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13097 i).upper ≤ (0.532 : ℝ) ∧
    (cell13097 i).centre ≤ (0.1 : ℝ) ∧ (cell13097 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13097 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13097 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13097

/-! The local source numeric instances at 13097 have no network premises. -/
namespace BstLean.Part269.N13097
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13097)
open BstLean.Part268 (cell13097)

noncomputable def sourceNumerics13097 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13097 (cell13097 i)
      scalarRow13097.M scalarRow13097.H scalarRow13097.xi := by
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
    energy_allowance := scalarRow13097.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13097]
    centre_nonneg := (scalarRow13097.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13097])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13097
/-! Actual 13098 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13098
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13098 ≤ (1.035256220507 : ℝ) := by
  have hr : (114.446494048529 : ℝ) ≤ √(13098 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.446494048529 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13098 13098 (11 / 1000) ≤
    (0.008352260376 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13098) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.446494048529 : ℝ) ≤ √(13098 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13098)
  have hdiv : K / √(13098 : ℝ) ≤ K / 114.446494048529 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.446494048529 ≤ (0.008352260376 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13098.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13098 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13098 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13098 := gPlus_lower 13098
end BstLean.Part269.N13098

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13098
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035256220506 : ℝ) ≤ wn 13098 := by
  have hn : √(13098 : ℝ) ≤ 114.446494048530 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13098 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.446494048530 ≤ 2 / √(13098 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244096748 : ℝ) ≤ rhoBar 13098 BstLean.Part154.csC ∧
    rhoBar 13098 BstLean.Part154.csC ≤ 0.000244097126 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035256220506 : ℝ) / (1.295212 * 13098) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035256220507 : ℝ) / (1.29521 * 13098) := by gcongr
      _ ≤ (0.000244097126 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13098 BstLean.Part154.csC) ≤ 0.000976448088 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13098 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13098 BstLean.Part154.csC) (piBar (rhoBar 13098 BstLean.Part154.csC)) ≤ 0.000186442764 ∧
    cc1 (rhoBar 13098 BstLean.Part154.csC) (piBar (rhoBar 13098 BstLean.Part154.csC)) ≤ 0.000118634823 ∧
    cc2 (rhoBar 13098 BstLean.Part154.csC) ≤ 0.000068868491 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13098 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13098 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13098 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13098 BstLean.Part154.csC * nuR (rhoBar 13098 BstLean.Part154.csC)) ≤ 0.000488209148 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244097126 : ℝ) * 0.000976448088 := by gcongr
      _ ≤ (0.000488209148 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13098 BstLean.Part154.csC) * nuR (rhoBar 13098 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000976448088 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13098 BstLean.Part154.csC) * rhoBar 13098 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244097126 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244097126 / 2 + 0.399 * 0.000976448088 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186442764 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488209148 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118634823 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244097126 / 1.414213562 := by gcongr
      _ ≤ (0.000068868491 : ℝ) := by norm_num

end BstLean.Part269.N13098

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13098
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13098 BstLean.Part154.csC) (piBar (rhoBar 13098 BstLean.Part154.csC)) ≤ 1.50116E-7 := by
  have hr0 : 0 ≤ rhoBar 13098 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13098 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13098 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13098 BstLean.Part154.csC) (piBar (rhoBar 13098 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13098 BstLean.Part154.csC) (piBar (rhoBar 13098 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13098 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186442764 : ℝ) ^ 2 + 0.000118634823 ^ 2 + 3 * 0.000068868491 ^ 2 +
        2 * 0.797885 * 0.000186442764 * 0.000118634823 + 2 * 0.000186442764 * 0.000068868491 +
        4 * 0.797885 * 0.000118634823 * 0.000068868491 := by gcongr
    _ ≤ (1.50116E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13098 BstLean.Part154.csC Θ ≤ 0.002546670926 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13098 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13098 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13098 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13098 BstLean.Part154.csC) (piBar (rhoBar 13098 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13098 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035256220507 * 1.50116E-7 / (0.000244096748 : ℝ) := by gcongr
    _ ≤ 0.002546670926 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13098 BstLean.Part154.csC Θ ≤ 0.002824157208 + 0.000643503213 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13098 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13098 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13098 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035256220507 : ℝ) * ((2 * Θ * 0.000244097126 +
        (6863 / 10000) * 0.000244097126 * 13098 * 0.000976448088) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002824157208 + 0.000643503213 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13098 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13098 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13098 0.011 Θ ∧ gammaRatio 13098 0.011 Θ ≤ 0.000083914280 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13098 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035256220507 : ℝ) * 0.525 / ((1 - 0.011) * 13098) := by gcongr
      _ ≤ (0.000083914280 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13098 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13098 0.011 Θ) :=
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
    badAllowance 13098 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13098 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13098 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13098 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13098 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13098 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13098 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13098 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13098 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13098 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13098 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035256220507 : ℝ) * 13098 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13098 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003172409556 + 0.003190174139 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13098

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13098
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13098 BstLean.Part154.csC) (piBar (rhoBar 13098 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13098 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13098 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13098 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13098 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13098 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13098 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13098 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13098 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13098 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13098 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13098 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13098 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13098 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13098 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051672179019 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13098) ≤ 0.010434898780 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13098 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035256220507)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010434898780 + 2 * 0.737676 / 13098) := by gcongr
    _ ≤ (0.051672179019 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13098 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13098

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13098
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521020117 : ℝ) ≤ plow 13098 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13098) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353850979)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337002237) : eMP 13098 0.011 xi bn ≤ 0.001151557006 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13098 : ℝ) * (1 - 0.011))) ≤ 0.000569430059 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001337002237 / (13098 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569430059 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569430059 : ℝ) + 3.141593 * 0.052353850979 / (13098 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001151557006 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353850979)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337002237) : PiBarMP 13098 12 0.011 xi bn ≤ 0.158757918822 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13098 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036565041187 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.815297741560 : ℝ) ≤ √((13098 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.446494048529 : ℝ) ≤ √(13098 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13098) ≤ 0.121737309462 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036565041187 + 0.052353850979 * 1.772454 / (2 * (113.815297741560 : ℝ))) * (1 + 0.001151557006) +
        8 / (13098 * 114.446494048529) + 0.121737309462 := by gcongr
    _ ≤ (0.158757918822 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353850979)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337002237) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280481818194) :
    parallelOracle 13098 0.011 xi bn cd ≤ 0.159718163579 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13098 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13098 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521020117 : ℝ) ≤ plow 13098 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.446494048529 : ℝ) ≤ √(13098 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280481818194 : ℝ) / (2 * 0.560521020117 * 114.446494048529)) * 0.158757918822 +
        0.280481818194 ^ 2 / (2 * 0.560521020117 * 114.446494048529) := by gcongr
    _ ≤ (0.159718163579 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353850979) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001337002237)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280481818194) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13098 13098 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521020117 : ℝ) ≤ plow 13098 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.446494048529 : ℝ) ≤ √(13098 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13098 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13098 Θ 1.22 ≤ 0.011587078408 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.446494048529 := by gcongr <;> linarith
      _ ≤ (0.011587078408 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13098 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13098 13098 0.011 ≤ 0.008352260376 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13098 13098 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13098 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13098 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13098 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13098 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159718163579 + 0.011587078408 + (0.008352260376 : ℝ) *
        (1 + 2 * (0.280481818194 + 0.011587078408) / (0.560521020117 * 114.446494048529))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13098]

end BstLean.Part269.N13098

/-! The original eight local profiles supply actual 13098 moment certificates. -/
namespace BstLean.Part269.N13098
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13098 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13098 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13098 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052353850979 ∧
    0 ≤ bN 13098 BstLean.Part154.csC (groupTheta g) ∧ bN 13098 BstLean.Part154.csC (groupTheta g) ≤ 0.001337002237 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13098 13098 0.011
      (momentAllowance 13098 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13098 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13098 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13098 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13098 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13098 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228809639175 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13098 0.011
      (momentAllowance 13098 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13098 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13098
/-! The actual computed-centre upper energy formula at 13098. -/
namespace BstLean.Part269.N13098
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13098

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13098
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13098)
open BstLean.Part268 (cell13098)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084407255009
  | 2 => 0.085332672710
  | 3 => 0.086253815683
  | 4 => 0.087171534214
  | 5 => 0.088086873064
  | 6 => 0.089001102337
  | 7 => 0.089915751654
  | 8 => 0.090832647710
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13098 13098 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13098 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003177634099 + 0.003195984085 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S29.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13098

/-! Actual upper energy certificates on all 43 source endpoints at 13098. -/
namespace BstLean.Part269.N13098
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13098)
open BstLean.Part268 (cell13098)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13098 (gMinus 13098) (1 - (cell13098 i).lower) ≤ 1 ∧
    energyUpper 13098 (gMinus 13098) (BstLean.Part211.gPlus 13098)
      (finiteEnergy 13098 13098 0.011) (1 - (cell13098 i).lower) ≤
      (cell13098 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨10,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨11,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨12,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨13,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨14,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨15,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨16,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨17,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨18,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨19,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨20,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨21,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨22,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨23,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨24,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨25,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨26,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨27,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨28,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨29,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨30,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨31,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨32,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨33,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨34,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨35,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨36,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨37,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨38,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨39,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨40,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨41,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨42,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨43,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨44,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨45,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨46,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨47,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨48,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨49,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨50,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨51,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13098) (by norm_num)
        (q := 1 - (cell13098 ⟨52,by decide⟩).lower)
        (by norm_num [cell13098]) (by norm_num [cell13098])
      exact ⟨E.1,E.2.trans (by norm_num [cell13098])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13098

/-! Source-cell containment and simple scalar guards at 13098. -/
namespace BstLean.Part269.N13098
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13098)
open BstLean.Part268 (cell13098)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13098 ⟨10,by decide⟩).lower ∧ (cell13098 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13098 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13098 ⟨11,by decide⟩).lower ∧ (cell13098 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13098 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13098 ⟨12,by decide⟩).lower ∧ (cell13098 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13098 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13098 ⟨13,by decide⟩).lower ∧ (cell13098 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13098 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13098 ⟨14,by decide⟩).lower ∧ (cell13098 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13098 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13098 ⟨15,by decide⟩).lower ∧ (cell13098 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13098 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13098 ⟨16,by decide⟩).lower ∧ (cell13098 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13098 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13098 ⟨17,by decide⟩).lower ∧ (cell13098 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13098 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13098 ⟨18,by decide⟩).lower ∧ (cell13098 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13098 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13098 ⟨19,by decide⟩).lower ∧ (cell13098 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13098 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13098 ⟨20,by decide⟩).lower ∧ (cell13098 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13098 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13098 ⟨21,by decide⟩).lower ∧ (cell13098 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13098 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13098 ⟨22,by decide⟩).lower ∧ (cell13098 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13098 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13098 ⟨23,by decide⟩).lower ∧ (cell13098 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13098 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13098 ⟨24,by decide⟩).lower ∧ (cell13098 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13098 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13098 ⟨25,by decide⟩).lower ∧ (cell13098 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13098 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13098 ⟨26,by decide⟩).lower ∧ (cell13098 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13098 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13098 ⟨27,by decide⟩).lower ∧ (cell13098 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13098 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13098 ⟨28,by decide⟩).lower ∧ (cell13098 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13098 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13098 ⟨29,by decide⟩).lower ∧ (cell13098 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13098 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13098 ⟨30,by decide⟩).lower ∧ (cell13098 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13098 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13098 ⟨31,by decide⟩).lower ∧ (cell13098 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13098 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13098 ⟨32,by decide⟩).lower ∧ (cell13098 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13098 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13098 ⟨33,by decide⟩).lower ∧ (cell13098 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13098 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13098 ⟨34,by decide⟩).lower ∧ (cell13098 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13098 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13098 ⟨35,by decide⟩).lower ∧ (cell13098 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13098 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13098 ⟨36,by decide⟩).lower ∧ (cell13098 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13098 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13098 ⟨37,by decide⟩).lower ∧ (cell13098 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13098 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13098 ⟨38,by decide⟩).lower ∧ (cell13098 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13098 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13098 ⟨39,by decide⟩).lower ∧ (cell13098 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13098 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13098 ⟨40,by decide⟩).lower ∧ (cell13098 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13098 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13098 ⟨41,by decide⟩).lower ∧ (cell13098 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13098 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13098 ⟨42,by decide⟩).lower ∧ (cell13098 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13098 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13098 ⟨43,by decide⟩).lower ∧ (cell13098 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13098 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13098 ⟨44,by decide⟩).lower ∧ (cell13098 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13098 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13098 ⟨45,by decide⟩).lower ∧ (cell13098 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13098 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13098 ⟨46,by decide⟩).lower ∧ (cell13098 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13098 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13098 ⟨47,by decide⟩).lower ∧ (cell13098 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13098 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13098 ⟨48,by decide⟩).lower ∧ (cell13098 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13098 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13098 ⟨49,by decide⟩).lower ∧ (cell13098 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13098 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13098 ⟨50,by decide⟩).lower ∧ (cell13098 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13098 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13098 ⟨51,by decide⟩).lower ∧ (cell13098 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13098 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13098 ⟨52,by decide⟩).lower ∧ (cell13098 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13098 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13098 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13098 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13098,cell13098,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13098 i).lower ∧
    (cell13098 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13098 i).upper ≤ (0.532 : ℝ) ∧
    (cell13098 i).centre ≤ (0.1 : ℝ) ∧ (cell13098 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13098 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13098 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13098

/-! The local source numeric instances at 13098 have no network premises. -/
namespace BstLean.Part269.N13098
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13098)
open BstLean.Part268 (cell13098)

noncomputable def sourceNumerics13098 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13098 (cell13098 i)
      scalarRow13098.M scalarRow13098.H scalarRow13098.xi := by
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
    energy_allowance := scalarRow13098.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13098]
    centre_nonneg := (scalarRow13098.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13098])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13098
/-! Actual 13099 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13099
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13099 ≤ (1.035254863065 : ℝ) := by
  have hr : (114.450862818940 : ℝ) ≤ √(13099 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.450862818940 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13099 13099 (11 / 1000) ≤
    (0.008351941555 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13099) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.450862818940 : ℝ) ≤ √(13099 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13099)
  have hdiv : K / √(13099 : ℝ) ≤ K / 114.450862818940 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.450862818940 ≤ (0.008351941555 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13099.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13099 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13099 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13099 := gPlus_lower 13099
end BstLean.Part269.N13099

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13099
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035254863064 : ℝ) ≤ wn 13099 := by
  have hn : √(13099 : ℝ) ≤ 114.450862818941 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13099 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.450862818941 ≤ 2 / √(13099 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244077793 : ℝ) ≤ rhoBar 13099 BstLean.Part154.csC ∧
    rhoBar 13099 BstLean.Part154.csC ≤ 0.000244078171 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035254863064 : ℝ) / (1.295212 * 13099) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035254863065 : ℝ) / (1.29521 * 13099) := by gcongr
      _ ≤ (0.000244078171 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13099 BstLean.Part154.csC) ≤ 0.000976372259 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13099 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13099 BstLean.Part154.csC) (piBar (rhoBar 13099 BstLean.Part154.csC)) ≤ 0.000186428285 ∧
    cc1 (rhoBar 13099 BstLean.Part154.csC) (piBar (rhoBar 13099 BstLean.Part154.csC)) ≤ 0.000118625611 ∧
    cc2 (rhoBar 13099 BstLean.Part154.csC) ≤ 0.000068863143 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13099 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13099 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13099 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13099 BstLean.Part154.csC * nuR (rhoBar 13099 BstLean.Part154.csC)) ≤ 0.000488171236 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244078171 : ℝ) * 0.000976372259 := by gcongr
      _ ≤ (0.000488171236 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13099 BstLean.Part154.csC) * nuR (rhoBar 13099 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000976372259 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13099 BstLean.Part154.csC) * rhoBar 13099 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244078171 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244078171 / 2 + 0.399 * 0.000976372259 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186428285 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488171236 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118625611 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244078171 / 1.414213562 := by gcongr
      _ ≤ (0.000068863143 : ℝ) := by norm_num

end BstLean.Part269.N13099

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13099
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13099 BstLean.Part154.csC) (piBar (rhoBar 13099 BstLean.Part154.csC)) ≤ 1.50093E-7 := by
  have hr0 : 0 ≤ rhoBar 13099 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13099 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13099 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13099 BstLean.Part154.csC) (piBar (rhoBar 13099 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13099 BstLean.Part154.csC) (piBar (rhoBar 13099 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13099 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186428285 : ℝ) ^ 2 + 0.000118625611 ^ 2 + 3 * 0.000068863143 ^ 2 +
        2 * 0.797885 * 0.000186428285 * 0.000118625611 + 2 * 0.000186428285 * 0.000068863143 +
        4 * 0.797885 * 0.000118625611 * 0.000068863143 := by gcongr
    _ ≤ (1.50093E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13099 BstLean.Part154.csC Θ ≤ 0.002546475143 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13099 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13099 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13099 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13099 BstLean.Part154.csC) (piBar (rhoBar 13099 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13099 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035254863065 * 1.50093E-7 / (0.000244077793 : ℝ) := by gcongr
    _ ≤ 0.002546475143 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13099 BstLean.Part154.csC Θ ≤ 0.002823930482 + 0.000643452399 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13099 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13099 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13099 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035254863065 : ℝ) * ((2 * Θ * 0.000244078171 +
        (6863 / 10000) * 0.000244078171 * 13099 * 0.000976372259) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002823930482 + 0.000643452399 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13099 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13099 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13099 0.011 Θ ∧ gammaRatio 13099 0.011 Θ ≤ 0.000083907764 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13099 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035254863065 : ℝ) * 0.525 / ((1 - 0.011) * 13099) := by gcongr
      _ ≤ (0.000083907764 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13099 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13099 0.011 Θ) :=
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
    badAllowance 13099 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13099 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13099 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13099 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13099 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13099 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13099 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13099 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13099 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13099 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13099 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035254863065 : ℝ) * 13099 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13099 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003172182830 + 0.003189927542 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13099

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13099
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13099 BstLean.Part154.csC) (piBar (rhoBar 13099 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13099 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13099 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13099 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13099 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13099 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13099 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13099 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13099 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13099 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13099 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13099 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13099 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13099 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13099 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051670185546 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13099) ≤ 0.010434500463 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13099 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035254863065)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010434500463 + 2 * 0.737676 / 13099) := by gcongr
    _ ≤ (0.051670185546 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13099 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13099

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13099
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560521062630 : ℝ) ≤ plow 13099 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13099) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353494790)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336899451) : eMP 13099 0.011 xi bn ≤ 0.001151468702 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13099 : ℝ) * (1 - 0.011))) ≤ 0.000569386435 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001336899451 / (13099 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569386435 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569386435 : ℝ) + 3.141593 * 0.052353494790 / (13099 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001151468702 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353494790)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336899451) : PiBarMP 13099 12 0.011 xi bn ≤ 0.158751842517 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13099 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036563635638 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.819642417291 : ℝ) ≤ √((13099 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.450862818940 : ℝ) ≤ √(13099 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13099) ≤ 0.121732662556 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036563635638 + 0.052353494790 * 1.772454 / (2 * (113.819642417291 : ℝ))) * (1 + 0.001151468702) +
        8 / (13099 * 114.450862818940) + 0.121732662556 := by gcongr
    _ ≤ (0.158751842517 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353494790)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336899451) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280479046367) :
    parallelOracle 13099 0.011 xi bn cd ≤ 0.159712021716 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13099 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13099 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560521062630 : ℝ) ≤ plow 13099 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.450862818940 : ℝ) ≤ √(13099 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280479046367 : ℝ) / (2 * 0.560521062630 * 114.450862818940)) * 0.158751842517 +
        0.280479046367 ^ 2 / (2 * 0.560521062630 * 114.450862818940) := by gcongr
    _ ≤ (0.159712021716 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052353494790) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001336899451)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280479046367) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13099 13099 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560521062630 : ℝ) ≤ plow 13099 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.450862818940 : ℝ) ≤ √(13099 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13099 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13099 Θ 1.22 ≤ 0.011586636111 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.450862818940 := by gcongr <;> linarith
      _ ≤ (0.011586636111 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13099 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13099 13099 0.011 ≤ 0.008351941555 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13099 13099 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13099 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13099 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13099 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13099 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159712021716 + 0.011586636111 + (0.008351941555 : ℝ) *
        (1 + 2 * (0.280479046367 + 0.011586636111) / (0.560521062630 * 114.450862818940))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13099]

end BstLean.Part269.N13099

/-! The original eight local profiles supply actual 13099 moment certificates. -/
namespace BstLean.Part269.N13099
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13099 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13099 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13099 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052353494790 ∧
    0 ≤ bN 13099 BstLean.Part154.csC (groupTheta g) ∧ bN 13099 BstLean.Part154.csC (groupTheta g) ≤ 0.001336899451 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13099 13099 0.011
      (momentAllowance 13099 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13099 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13099 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13099 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13099 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13099 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228808860821 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13099 0.011
      (momentAllowance 13099 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13099 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13099
/-! The actual computed-centre upper energy formula at 13099. -/
namespace BstLean.Part269.N13099
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13099

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13099
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13099)
open BstLean.Part268 (cell13099)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084404712465
  | 2 => 0.085330098244
  | 3 => 0.086251204671
  | 4 => 0.087168880936
  | 5 => 0.088084170496
  | 6 => 0.088998341925
  | 7 => 0.089912923049
  | 8 => 0.090829738482
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13099 13099 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13099 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003177634099 + 0.003195984085 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S29.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S29.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13099

/-! Actual upper energy certificates on all 43 source endpoints at 13099. -/
namespace BstLean.Part269.N13099
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13099)
open BstLean.Part268 (cell13099)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13099 (gMinus 13099) (1 - (cell13099 i).lower) ≤ 1 ∧
    energyUpper 13099 (gMinus 13099) (BstLean.Part211.gPlus 13099)
      (finiteEnergy 13099 13099 0.011) (1 - (cell13099 i).lower) ≤
      (cell13099 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨10,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨11,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨12,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨13,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨14,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨15,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨16,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨17,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨18,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨19,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨20,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨21,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨22,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨23,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨24,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨25,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨26,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨27,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨28,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨29,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨30,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨31,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨32,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨33,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨34,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨35,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨36,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨37,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨38,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨39,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨40,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨41,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨42,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨43,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨44,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨45,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨46,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨47,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨48,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨49,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨50,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨51,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13099) (by norm_num)
        (q := 1 - (cell13099 ⟨52,by decide⟩).lower)
        (by norm_num [cell13099]) (by norm_num [cell13099])
      exact ⟨E.1,E.2.trans (by norm_num [cell13099])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13099

/-! Source-cell containment and simple scalar guards at 13099. -/
namespace BstLean.Part269.N13099
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13099)
open BstLean.Part268 (cell13099)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13099 ⟨10,by decide⟩).lower ∧ (cell13099 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13099 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13099 ⟨11,by decide⟩).lower ∧ (cell13099 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13099 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13099 ⟨12,by decide⟩).lower ∧ (cell13099 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13099 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13099 ⟨13,by decide⟩).lower ∧ (cell13099 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13099 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13099 ⟨14,by decide⟩).lower ∧ (cell13099 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13099 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13099 ⟨15,by decide⟩).lower ∧ (cell13099 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13099 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13099 ⟨16,by decide⟩).lower ∧ (cell13099 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13099 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13099 ⟨17,by decide⟩).lower ∧ (cell13099 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13099 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13099 ⟨18,by decide⟩).lower ∧ (cell13099 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13099 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13099 ⟨19,by decide⟩).lower ∧ (cell13099 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13099 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13099 ⟨20,by decide⟩).lower ∧ (cell13099 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13099 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13099 ⟨21,by decide⟩).lower ∧ (cell13099 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13099 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13099 ⟨22,by decide⟩).lower ∧ (cell13099 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13099 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13099 ⟨23,by decide⟩).lower ∧ (cell13099 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13099 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13099 ⟨24,by decide⟩).lower ∧ (cell13099 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13099 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13099 ⟨25,by decide⟩).lower ∧ (cell13099 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13099 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13099 ⟨26,by decide⟩).lower ∧ (cell13099 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13099 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13099 ⟨27,by decide⟩).lower ∧ (cell13099 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13099 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13099 ⟨28,by decide⟩).lower ∧ (cell13099 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13099 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13099 ⟨29,by decide⟩).lower ∧ (cell13099 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13099 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13099 ⟨30,by decide⟩).lower ∧ (cell13099 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13099 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13099 ⟨31,by decide⟩).lower ∧ (cell13099 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13099 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13099 ⟨32,by decide⟩).lower ∧ (cell13099 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13099 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13099 ⟨33,by decide⟩).lower ∧ (cell13099 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13099 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13099 ⟨34,by decide⟩).lower ∧ (cell13099 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13099 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13099 ⟨35,by decide⟩).lower ∧ (cell13099 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13099 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13099 ⟨36,by decide⟩).lower ∧ (cell13099 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13099 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13099 ⟨37,by decide⟩).lower ∧ (cell13099 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13099 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13099 ⟨38,by decide⟩).lower ∧ (cell13099 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13099 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13099 ⟨39,by decide⟩).lower ∧ (cell13099 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13099 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13099 ⟨40,by decide⟩).lower ∧ (cell13099 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13099 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13099 ⟨41,by decide⟩).lower ∧ (cell13099 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13099 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13099 ⟨42,by decide⟩).lower ∧ (cell13099 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13099 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13099 ⟨43,by decide⟩).lower ∧ (cell13099 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13099 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13099 ⟨44,by decide⟩).lower ∧ (cell13099 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13099 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13099 ⟨45,by decide⟩).lower ∧ (cell13099 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13099 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13099 ⟨46,by decide⟩).lower ∧ (cell13099 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13099 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13099 ⟨47,by decide⟩).lower ∧ (cell13099 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13099 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13099 ⟨48,by decide⟩).lower ∧ (cell13099 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13099 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13099 ⟨49,by decide⟩).lower ∧ (cell13099 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13099 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13099 ⟨50,by decide⟩).lower ∧ (cell13099 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13099 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13099 ⟨51,by decide⟩).lower ∧ (cell13099 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13099 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13099 ⟨52,by decide⟩).lower ∧ (cell13099 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13099 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13099 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13099 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13099,cell13099,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13099 i).lower ∧
    (cell13099 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13099 i).upper ≤ (0.532 : ℝ) ∧
    (cell13099 i).centre ≤ (0.1 : ℝ) ∧ (cell13099 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13099 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13099 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13099

/-! The local source numeric instances at 13099 have no network premises. -/
namespace BstLean.Part269.N13099
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13099)
open BstLean.Part268 (cell13099)

noncomputable def sourceNumerics13099 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13099 (cell13099 i)
      scalarRow13099.M scalarRow13099.H scalarRow13099.xi := by
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
    energy_allowance := scalarRow13099.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13099]
    centre_nonneg := (scalarRow13099.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13099])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13099