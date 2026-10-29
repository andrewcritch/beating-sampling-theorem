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
/-! Actual 13075 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13075
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13075 ≤ (1.035287484898 : ℝ) := by
  have hr : (114.345966260292 : ℝ) ≤ √(13075 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.345966260292 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13075 13075 (11 / 1000) ≤
    (0.008359603360 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13075) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.345966260292 : ℝ) ≤ √(13075 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13075)
  have hdiv : K / √(13075 : ℝ) ≤ K / 114.345966260292 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.345966260292 ≤ (0.008359603360 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13075.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13075 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13075 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13075 := gPlus_lower 13075
end BstLean.Part269.N13075

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13075
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035287484897 : ℝ) ≤ wn 13075 := by
  have hn : √(13075 : ℝ) ≤ 114.345966260293 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13075 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.345966260293 ≤ 2 / √(13075 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244533519 : ℝ) ≤ rhoBar 13075 BstLean.Part154.csC ∧
    rhoBar 13075 BstLean.Part154.csC ≤ 0.000244533897 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035287484897 : ℝ) / (1.295212 * 13075) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035287484898 : ℝ) / (1.29521 * 13075) := by gcongr
      _ ≤ (0.000244533897 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13075 BstLean.Part154.csC) ≤ 0.000978195385 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13075 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13075 BstLean.Part154.csC) (piBar (rhoBar 13075 BstLean.Part154.csC)) ≤ 0.000186776387 ∧
    cc1 (rhoBar 13075 BstLean.Part154.csC) (piBar (rhoBar 13075 BstLean.Part154.csC)) ≤ 0.000118847107 ∧
    cc2 (rhoBar 13075 BstLean.Part154.csC) ≤ 0.000068991720 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13075 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13075 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13075 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13075 BstLean.Part154.csC * nuR (rhoBar 13075 BstLean.Part154.csC)) ≤ 0.000489082744 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244533897 : ℝ) * 0.000978195385 := by gcongr
      _ ≤ (0.000489082744 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13075 BstLean.Part154.csC) * nuR (rhoBar 13075 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000978195385 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13075 BstLean.Part154.csC) * rhoBar 13075 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244533897 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244533897 / 2 + 0.399 * 0.000978195385 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186776387 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489082744 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118847107 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244533897 / 1.414213562 := by gcongr
      _ ≤ (0.000068991720 : ℝ) := by norm_num

end BstLean.Part269.N13075

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13075
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13075 BstLean.Part154.csC) (piBar (rhoBar 13075 BstLean.Part154.csC)) ≤ 1.50654E-7 := by
  have hr0 : 0 ≤ rhoBar 13075 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13075 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13075 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13075 BstLean.Part154.csC) (piBar (rhoBar 13075 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13075 BstLean.Part154.csC) (piBar (rhoBar 13075 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13075 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186776387 : ℝ) ^ 2 + 0.000118847107 ^ 2 + 3 * 0.000068991720 ^ 2 +
        2 * 0.797885 * 0.000186776387 * 0.000118847107 + 2 * 0.000186776387 * 0.000068991720 +
        4 * 0.797885 * 0.000118847107 * 0.000068991720 := by gcongr
    _ ≤ (1.50654E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13075 BstLean.Part154.csC Θ ≤ 0.002551309962 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13075 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13075 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13075 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13075 BstLean.Part154.csC) (piBar (rhoBar 13075 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13075 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035287484898 * 1.50654E-7 / (0.000244533519 : ℝ) := by gcongr
    _ ≤ 0.002551309962 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13075 BstLean.Part154.csC Θ ≤ 0.002829381751 + 0.000644674123 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13075 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13075 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13075 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035287484898 : ℝ) * ((2 * Θ * 0.000244533897 +
        (6863 / 10000) * 0.000244533897 * 13075 * 0.000978195385) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002829381751 + 0.000644674123 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13075 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13075 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13075 0.011 Θ ∧ gammaRatio 13075 0.011 Θ ≤ 0.000084064431 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13075 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035287484898 : ℝ) * 0.525 / ((1 - 0.011) * 13075) := by gcongr
      _ ≤ (0.000084064431 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13075 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13075 0.011 Θ) :=
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
    badAllowance 13075 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13075 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13075 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13075 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13075 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13075 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13075 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13075 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13075 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13075 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13075 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035287484898 : ℝ) * 13075 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13075 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003177634099 + 0.003195984085 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13075

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13075
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13075 BstLean.Part154.csC) (piBar (rhoBar 13075 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13075 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13075 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13075 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13075 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13075 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13075 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13075 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13075 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13075 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13075 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13075 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13075 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13075 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13075 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051718092417 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13075) ≤ 0.010444072670 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13075 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035287484898)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010444072670 + 2 * 0.737676 / 13075) := by gcongr
    _ ≤ (0.051718092417 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13075 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13075

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13075
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520040520 : ℝ) ≤ plow 13075 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13075) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052362125744)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339437731) : eMP 13075 0.011 xi bn ≤ 0.001153620303 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13075 : ℝ) * (1 - 0.011))) ≤ 0.000570449535 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001339437731 / (13075 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570449535 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570449535 : ℝ) + 3.141593 * 0.052362125744 / (13075 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001153620303 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052362125744)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339437731) : PiBarMP 13075 12 0.011 xi bn ≤ 0.158898785322 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13075 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036598329621 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.715324385062 : ℝ) ≤ √((13075 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.345966260292 : ℝ) ≤ √(13075 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13075) ≤ 0.121844335384 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036598329621 + 0.052362125744 * 1.772454 / (2 * (113.715324385062 : ℝ))) * (1 + 0.001153620303) +
        8 / (13075 * 114.345966260292) + 0.121844335384 := by gcongr
    _ ≤ (0.158898785322 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052362125744)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339437731) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280545813081) :
    parallelOracle 13075 0.011 xi bn cd ≤ 0.159860543600 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13075 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13075 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520040520 : ℝ) ≤ plow 13075 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.345966260292 : ℝ) ≤ √(13075 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280545813081 : ℝ) / (2 * 0.560520040520 * 114.345966260292)) * 0.158898785322 +
        0.280545813081 ^ 2 / (2 * 0.560520040520 * 114.345966260292) := by gcongr
    _ ≤ (0.159860543600 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052362125744) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339437731)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280545813081) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13075 13075 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520040520 : ℝ) ≤ plow 13075 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.345966260292 : ℝ) ≤ √(13075 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13075 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13075 Θ 1.22 ≤ 0.011597265242 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.345966260292 := by gcongr <;> linarith
      _ ≤ (0.011597265242 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13075 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13075 13075 0.011 ≤ 0.008359603360 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13075 13075 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13075 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13075 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13075 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13075 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159860543600 + 0.011597265242 + (0.008359603360 : ℝ) *
        (1 + 2 * (0.280545813081 + 0.011597265242) / (0.560520040520 * 114.345966260292))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13075]

end BstLean.Part269.N13075

/-! The original eight local profiles supply actual 13075 moment certificates. -/
namespace BstLean.Part269.N13075
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13075 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13075 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13075 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052362125744 ∧
    0 ≤ bN 13075 BstLean.Part154.csC (groupTheta g) ∧ bN 13075 BstLean.Part154.csC (groupTheta g) ≤ 0.001339437731 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13075 13075 0.011
      (momentAllowance 13075 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13075 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13075 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13075 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13075 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13075 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228827720664 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13075 0.011
      (momentAllowance 13075 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13075 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13075
/-! The actual computed-centre upper energy formula at 13075. -/
namespace BstLean.Part269.N13075
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13075

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13075
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13075)
open BstLean.Part268 (cell13075)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084465938766
  | 2 => 0.085392097686
  | 3 => 0.086314089898
  | 4 => 0.087232791307
  | 5 => 0.088149277024
  | 6 => 0.089064852873
  | 7 => 0.089981090234
  | 8 => 0.090899864329
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13075 13075 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13075 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13075

/-! Actual upper energy certificates on all 43 source endpoints at 13075. -/
namespace BstLean.Part269.N13075
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13075)
open BstLean.Part268 (cell13075)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13075 (gMinus 13075) (1 - (cell13075 i).lower) ≤ 1 ∧
    energyUpper 13075 (gMinus 13075) (BstLean.Part211.gPlus 13075)
      (finiteEnergy 13075 13075 0.011) (1 - (cell13075 i).lower) ≤
      (cell13075 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨10,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨11,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨12,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨13,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨14,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨15,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨16,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨17,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨18,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨19,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨20,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨21,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨22,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨23,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨24,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨25,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨26,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨27,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨28,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨29,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨30,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨31,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨32,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨33,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨34,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨35,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨36,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨37,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨38,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨39,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨40,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨41,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨42,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨43,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨44,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨45,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨46,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨47,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨48,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨49,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨50,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨51,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13075) (by norm_num)
        (q := 1 - (cell13075 ⟨52,by decide⟩).lower)
        (by norm_num [cell13075]) (by norm_num [cell13075])
      exact ⟨E.1,E.2.trans (by norm_num [cell13075])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13075

/-! Source-cell containment and simple scalar guards at 13075. -/
namespace BstLean.Part269.N13075
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13075)
open BstLean.Part268 (cell13075)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13075 ⟨10,by decide⟩).lower ∧ (cell13075 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13075 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13075 ⟨11,by decide⟩).lower ∧ (cell13075 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13075 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13075 ⟨12,by decide⟩).lower ∧ (cell13075 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13075 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13075 ⟨13,by decide⟩).lower ∧ (cell13075 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13075 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13075 ⟨14,by decide⟩).lower ∧ (cell13075 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13075 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13075 ⟨15,by decide⟩).lower ∧ (cell13075 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13075 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13075 ⟨16,by decide⟩).lower ∧ (cell13075 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13075 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13075 ⟨17,by decide⟩).lower ∧ (cell13075 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13075 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13075 ⟨18,by decide⟩).lower ∧ (cell13075 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13075 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13075 ⟨19,by decide⟩).lower ∧ (cell13075 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13075 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13075 ⟨20,by decide⟩).lower ∧ (cell13075 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13075 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13075 ⟨21,by decide⟩).lower ∧ (cell13075 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13075 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13075 ⟨22,by decide⟩).lower ∧ (cell13075 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13075 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13075 ⟨23,by decide⟩).lower ∧ (cell13075 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13075 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13075 ⟨24,by decide⟩).lower ∧ (cell13075 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13075 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13075 ⟨25,by decide⟩).lower ∧ (cell13075 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13075 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13075 ⟨26,by decide⟩).lower ∧ (cell13075 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13075 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13075 ⟨27,by decide⟩).lower ∧ (cell13075 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13075 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13075 ⟨28,by decide⟩).lower ∧ (cell13075 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13075 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13075 ⟨29,by decide⟩).lower ∧ (cell13075 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13075 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13075 ⟨30,by decide⟩).lower ∧ (cell13075 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13075 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13075 ⟨31,by decide⟩).lower ∧ (cell13075 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13075 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13075 ⟨32,by decide⟩).lower ∧ (cell13075 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13075 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13075 ⟨33,by decide⟩).lower ∧ (cell13075 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13075 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13075 ⟨34,by decide⟩).lower ∧ (cell13075 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13075 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13075 ⟨35,by decide⟩).lower ∧ (cell13075 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13075 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13075 ⟨36,by decide⟩).lower ∧ (cell13075 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13075 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13075 ⟨37,by decide⟩).lower ∧ (cell13075 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13075 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13075 ⟨38,by decide⟩).lower ∧ (cell13075 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13075 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13075 ⟨39,by decide⟩).lower ∧ (cell13075 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13075 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13075 ⟨40,by decide⟩).lower ∧ (cell13075 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13075 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13075 ⟨41,by decide⟩).lower ∧ (cell13075 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13075 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13075 ⟨42,by decide⟩).lower ∧ (cell13075 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13075 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13075 ⟨43,by decide⟩).lower ∧ (cell13075 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13075 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13075 ⟨44,by decide⟩).lower ∧ (cell13075 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13075 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13075 ⟨45,by decide⟩).lower ∧ (cell13075 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13075 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13075 ⟨46,by decide⟩).lower ∧ (cell13075 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13075 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13075 ⟨47,by decide⟩).lower ∧ (cell13075 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13075 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13075 ⟨48,by decide⟩).lower ∧ (cell13075 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13075 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13075 ⟨49,by decide⟩).lower ∧ (cell13075 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13075 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13075 ⟨50,by decide⟩).lower ∧ (cell13075 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13075 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13075 ⟨51,by decide⟩).lower ∧ (cell13075 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13075 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13075 ⟨52,by decide⟩).lower ∧ (cell13075 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13075 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13075 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13075 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13075,cell13075,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13075 i).lower ∧
    (cell13075 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13075 i).upper ≤ (0.532 : ℝ) ∧
    (cell13075 i).centre ≤ (0.1 : ℝ) ∧ (cell13075 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13075 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13075 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13075

/-! The local source numeric instances at 13075 have no network premises. -/
namespace BstLean.Part269.N13075
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13075)
open BstLean.Part268 (cell13075)

noncomputable def sourceNumerics13075 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13075 (cell13075 i)
      scalarRow13075.M scalarRow13075.H scalarRow13075.xi := by
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
    energy_allowance := scalarRow13075.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13075]
    centre_nonneg := (scalarRow13075.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13075])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13075
/-! Actual 13076 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13076
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13076 ≤ (1.035286123852 : ℝ) := by
  have hr : (114.350338871382 : ℝ) ≤ √(13076 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.350338871382 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13076 13076 (11 / 1000) ≤
    (0.008359283697 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13076) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.350338871382 : ℝ) ≤ √(13076 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13076)
  have hdiv : K / √(13076 : ℝ) ≤ K / 114.350338871382 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.350338871382 ≤ (0.008359283697 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13076.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13076 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13076 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13076 := gPlus_lower 13076
end BstLean.Part269.N13076

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13076
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035286123851 : ℝ) ≤ wn 13076 := by
  have hn : √(13076 : ℝ) ≤ 114.350338871383 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13076 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.350338871383 ≤ 2 / √(13076 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244514497 : ℝ) ≤ rhoBar 13076 BstLean.Part154.csC ∧
    rhoBar 13076 BstLean.Part154.csC ≤ 0.000244514875 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035286123851 : ℝ) / (1.295212 * 13076) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035286123852 : ℝ) / (1.29521 * 13076) := by gcongr
      _ ≤ (0.000244514875 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13076 BstLean.Part154.csC) ≤ 0.000978119288 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13076 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13076 BstLean.Part154.csC) (piBar (rhoBar 13076 BstLean.Part154.csC)) ≤ 0.000186761857 ∧
    cc1 (rhoBar 13076 BstLean.Part154.csC) (piBar (rhoBar 13076 BstLean.Part154.csC)) ≤ 0.000118837862 ∧
    cc2 (rhoBar 13076 BstLean.Part154.csC) ≤ 0.000068986353 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13076 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13076 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13076 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13076 BstLean.Part154.csC * nuR (rhoBar 13076 BstLean.Part154.csC)) ≤ 0.000489044697 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244514875 : ℝ) * 0.000978119288 := by gcongr
      _ ≤ (0.000489044697 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13076 BstLean.Part154.csC) * nuR (rhoBar 13076 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000978119288 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13076 BstLean.Part154.csC) * rhoBar 13076 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244514875 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244514875 / 2 + 0.399 * 0.000978119288 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186761857 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489044697 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118837862 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244514875 / 1.414213562 := by gcongr
      _ ≤ (0.000068986353 : ℝ) := by norm_num

end BstLean.Part269.N13076

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13076
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13076 BstLean.Part154.csC) (piBar (rhoBar 13076 BstLean.Part154.csC)) ≤ 1.50630E-7 := by
  have hr0 : 0 ≤ rhoBar 13076 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13076 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13076 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13076 BstLean.Part154.csC) (piBar (rhoBar 13076 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13076 BstLean.Part154.csC) (piBar (rhoBar 13076 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13076 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186761857 : ℝ) ^ 2 + 0.000118837862 ^ 2 + 3 * 0.000068986353 ^ 2 +
        2 * 0.797885 * 0.000186761857 * 0.000118837862 + 2 * 0.000186761857 * 0.000068986353 +
        4 * 0.797885 * 0.000118837862 * 0.000068986353 := by gcongr
    _ ≤ (1.50630E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13076 BstLean.Part154.csC Θ ≤ 0.002551098618 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13076 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13076 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13076 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13076 BstLean.Part154.csC) (piBar (rhoBar 13076 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13076 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035286123852 * 1.50630E-7 / (0.000244514497 : ℝ) := by gcongr
    _ ≤ 0.002551098618 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13076 BstLean.Part154.csC Θ ≤ 0.002829154211 + 0.000644623127 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13076 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13076 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13076 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035286123852 : ℝ) * ((2 * Θ * 0.000244514875 +
        (6863 / 10000) * 0.000244514875 * 13076 * 0.000978119288) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002829154211 + 0.000644623127 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13076 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13076 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13076 0.011 Θ ∧ gammaRatio 13076 0.011 Θ ≤ 0.000084057891 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13076 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035286123852 : ℝ) * 0.525 / ((1 - 0.011) * 13076) := by gcongr
      _ ≤ (0.000084057891 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13076 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13076 0.011 Θ) :=
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
    badAllowance 13076 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13076 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13076 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13076 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13076 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13076 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13076 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13076 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13076 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13076 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13076 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035286123852 : ℝ) * 13076 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13076 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003177406559 + 0.003195721745 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13076

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13076
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13076 BstLean.Part154.csC) (piBar (rhoBar 13076 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13076 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13076 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13076 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13076 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13076 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13076 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13076 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13076 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13076 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13076 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13076 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13076 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13076 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13076 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051716093646 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13076) ≤ 0.010443673302 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13076 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035286123852)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010443673302 + 2 * 0.737676 / 13076) := by gcongr
    _ ≤ (0.051716093646 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13076 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13076

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13076
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520083182 : ℝ) ≤ plow 13076 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13076) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052361760476)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339326775) : eMP 13076 0.011 xi bn ≤ 0.001153528362 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13076 : ℝ) * (1 - 0.011))) ≤ 0.000570404095 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001339326775 / (13076 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570404095 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570404095 : ℝ) + 3.141593 * 0.052361760476 / (13076 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001153528362 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052361760476)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339326775) : PiBarMP 13076 12 0.011 xi bn ≤ 0.158892586020 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13076 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036596813728 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.719672880289 : ℝ) ≤ √((13076 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.350338871382 : ℝ) ≤ √(13076 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13076) ≤ 0.121839676212 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036596813728 + 0.052361760476 * 1.772454 / (2 * (113.719672880289 : ℝ))) * (1 + 0.001153528362) +
        8 / (13076 * 114.350338871382) + 0.121839676212 := by gcongr
    _ ≤ (0.158892586020 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052361760476)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339326775) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280543016180) :
    parallelOracle 13076 0.011 xi bn cd ≤ 0.159854278173 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13076 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13076 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520083182 : ℝ) ≤ plow 13076 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.350338871382 : ℝ) ≤ √(13076 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280543016180 : ℝ) / (2 * 0.560520083182 * 114.350338871382)) * 0.158892586020 +
        0.280543016180 ^ 2 / (2 * 0.560520083182 * 114.350338871382) := by gcongr
    _ ≤ (0.159854278173 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052361760476) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339326775)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280543016180) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13076 13076 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520083182 : ℝ) ≤ plow 13076 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.350338871382 : ℝ) ≤ √(13076 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13076 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13076 Θ 1.22 ≤ 0.011596821777 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.350338871382 := by gcongr <;> linarith
      _ ≤ (0.011596821777 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13076 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13076 13076 0.011 ≤ 0.008359283697 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13076 13076 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13076 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13076 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13076 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13076 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159854278173 + 0.011596821777 + (0.008359283697 : ℝ) *
        (1 + 2 * (0.280543016180 + 0.011596821777) / (0.560520083182 * 114.350338871382))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13076]

end BstLean.Part269.N13076

/-! The original eight local profiles supply actual 13076 moment certificates. -/
namespace BstLean.Part269.N13076
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13076 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13076 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13076 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052361760476 ∧
    0 ≤ bN 13076 BstLean.Part154.csC (groupTheta g) ∧ bN 13076 BstLean.Part154.csC (groupTheta g) ≤ 0.001339326775 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13076 13076 0.011
      (momentAllowance 13076 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13076 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13076 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13076 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13076 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13076 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228826922534 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13076 0.011
      (momentAllowance 13076 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13076 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13076
/-! The actual computed-centre upper energy formula at 13076. -/
namespace BstLean.Part269.N13076
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13076

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13076
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13076)
open BstLean.Part268 (cell13076)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084463379061
  | 2 => 0.085389505473
  | 3 => 0.086311460411
  | 4 => 0.087230118654
  | 5 => 0.088146553976
  | 6 => 0.089062070628
  | 7 => 0.089978238155
  | 8 => 0.090896929642
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13076 13076 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13076 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13076

/-! Actual upper energy certificates on all 43 source endpoints at 13076. -/
namespace BstLean.Part269.N13076
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13076)
open BstLean.Part268 (cell13076)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13076 (gMinus 13076) (1 - (cell13076 i).lower) ≤ 1 ∧
    energyUpper 13076 (gMinus 13076) (BstLean.Part211.gPlus 13076)
      (finiteEnergy 13076 13076 0.011) (1 - (cell13076 i).lower) ≤
      (cell13076 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨10,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨11,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨12,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨13,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨14,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨15,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨16,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨17,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨18,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨19,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨20,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨21,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨22,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨23,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨24,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨25,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨26,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨27,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨28,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨29,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨30,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨31,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨32,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨33,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨34,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨35,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨36,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨37,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨38,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨39,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨40,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨41,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨42,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨43,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨44,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨45,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨46,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨47,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨48,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨49,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨50,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨51,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13076) (by norm_num)
        (q := 1 - (cell13076 ⟨52,by decide⟩).lower)
        (by norm_num [cell13076]) (by norm_num [cell13076])
      exact ⟨E.1,E.2.trans (by norm_num [cell13076])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13076

/-! Source-cell containment and simple scalar guards at 13076. -/
namespace BstLean.Part269.N13076
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13076)
open BstLean.Part268 (cell13076)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13076 ⟨10,by decide⟩).lower ∧ (cell13076 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13076 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13076 ⟨11,by decide⟩).lower ∧ (cell13076 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13076 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13076 ⟨12,by decide⟩).lower ∧ (cell13076 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13076 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13076 ⟨13,by decide⟩).lower ∧ (cell13076 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13076 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13076 ⟨14,by decide⟩).lower ∧ (cell13076 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13076 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13076 ⟨15,by decide⟩).lower ∧ (cell13076 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13076 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13076 ⟨16,by decide⟩).lower ∧ (cell13076 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13076 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13076 ⟨17,by decide⟩).lower ∧ (cell13076 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13076 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13076 ⟨18,by decide⟩).lower ∧ (cell13076 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13076 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13076 ⟨19,by decide⟩).lower ∧ (cell13076 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13076 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13076 ⟨20,by decide⟩).lower ∧ (cell13076 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13076 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13076 ⟨21,by decide⟩).lower ∧ (cell13076 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13076 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13076 ⟨22,by decide⟩).lower ∧ (cell13076 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13076 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13076 ⟨23,by decide⟩).lower ∧ (cell13076 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13076 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13076 ⟨24,by decide⟩).lower ∧ (cell13076 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13076 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13076 ⟨25,by decide⟩).lower ∧ (cell13076 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13076 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13076 ⟨26,by decide⟩).lower ∧ (cell13076 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13076 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13076 ⟨27,by decide⟩).lower ∧ (cell13076 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13076 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13076 ⟨28,by decide⟩).lower ∧ (cell13076 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13076 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13076 ⟨29,by decide⟩).lower ∧ (cell13076 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13076 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13076 ⟨30,by decide⟩).lower ∧ (cell13076 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13076 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13076 ⟨31,by decide⟩).lower ∧ (cell13076 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13076 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13076 ⟨32,by decide⟩).lower ∧ (cell13076 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13076 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13076 ⟨33,by decide⟩).lower ∧ (cell13076 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13076 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13076 ⟨34,by decide⟩).lower ∧ (cell13076 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13076 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13076 ⟨35,by decide⟩).lower ∧ (cell13076 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13076 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13076 ⟨36,by decide⟩).lower ∧ (cell13076 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13076 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13076 ⟨37,by decide⟩).lower ∧ (cell13076 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13076 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13076 ⟨38,by decide⟩).lower ∧ (cell13076 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13076 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13076 ⟨39,by decide⟩).lower ∧ (cell13076 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13076 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13076 ⟨40,by decide⟩).lower ∧ (cell13076 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13076 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13076 ⟨41,by decide⟩).lower ∧ (cell13076 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13076 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13076 ⟨42,by decide⟩).lower ∧ (cell13076 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13076 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13076 ⟨43,by decide⟩).lower ∧ (cell13076 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13076 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13076 ⟨44,by decide⟩).lower ∧ (cell13076 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13076 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13076 ⟨45,by decide⟩).lower ∧ (cell13076 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13076 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13076 ⟨46,by decide⟩).lower ∧ (cell13076 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13076 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13076 ⟨47,by decide⟩).lower ∧ (cell13076 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13076 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13076 ⟨48,by decide⟩).lower ∧ (cell13076 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13076 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13076 ⟨49,by decide⟩).lower ∧ (cell13076 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13076 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13076 ⟨50,by decide⟩).lower ∧ (cell13076 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13076 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13076 ⟨51,by decide⟩).lower ∧ (cell13076 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13076 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13076 ⟨52,by decide⟩).lower ∧ (cell13076 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13076 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13076 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13076 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13076,cell13076,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13076 i).lower ∧
    (cell13076 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13076 i).upper ≤ (0.532 : ℝ) ∧
    (cell13076 i).centre ≤ (0.1 : ℝ) ∧ (cell13076 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13076 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13076 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13076

/-! The local source numeric instances at 13076 have no network premises. -/
namespace BstLean.Part269.N13076
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13076)
open BstLean.Part268 (cell13076)

noncomputable def sourceNumerics13076 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13076 (cell13076 i)
      scalarRow13076.M scalarRow13076.H scalarRow13076.xi := by
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
    energy_allowance := scalarRow13076.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13076]
    centre_nonneg := (scalarRow13076.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13076])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13076
/-! Actual 13077 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13077
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13077 ≤ (1.035284762963 : ℝ) := by
  have hr : (114.354711315275 : ℝ) ≤ √(13077 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.354711315275 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13077 13077 (11 / 1000) ≤
    (0.008358964071 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13077) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.354711315275 : ℝ) ≤ √(13077 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13077)
  have hdiv : K / √(13077 : ℝ) ≤ K / 114.354711315275 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.354711315275 ≤ (0.008358964071 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13077.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13077 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13077 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13077 := gPlus_lower 13077
end BstLean.Part269.N13077

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13077
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035284762962 : ℝ) ≤ wn 13077 := by
  have hn : √(13077 : ℝ) ≤ 114.354711315276 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13077 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.354711315276 ≤ 2 / √(13077 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244495477 : ℝ) ≤ rhoBar 13077 BstLean.Part154.csC ∧
    rhoBar 13077 BstLean.Part154.csC ≤ 0.000244495856 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035284762962 : ℝ) / (1.295212 * 13077) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035284762963 : ℝ) / (1.29521 * 13077) := by gcongr
      _ ≤ (0.000244495856 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13077 BstLean.Part154.csC) ≤ 0.000978043203 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13077 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13077 BstLean.Part154.csC) (piBar (rhoBar 13077 BstLean.Part154.csC)) ≤ 0.000186747330 ∧
    cc1 (rhoBar 13077 BstLean.Part154.csC) (piBar (rhoBar 13077 BstLean.Part154.csC)) ≤ 0.000118828618 ∧
    cc2 (rhoBar 13077 BstLean.Part154.csC) ≤ 0.000068980987 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13077 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13077 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13077 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13077 BstLean.Part154.csC * nuR (rhoBar 13077 BstLean.Part154.csC)) ≤ 0.000489006657 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244495856 : ℝ) * 0.000978043203 := by gcongr
      _ ≤ (0.000489006657 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13077 BstLean.Part154.csC) * nuR (rhoBar 13077 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000978043203 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13077 BstLean.Part154.csC) * rhoBar 13077 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244495856 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244495856 / 2 + 0.399 * 0.000978043203 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186747330 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000489006657 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118828618 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244495856 / 1.414213562 := by gcongr
      _ ≤ (0.000068980987 : ℝ) := by norm_num

end BstLean.Part269.N13077

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13077
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13077 BstLean.Part154.csC) (piBar (rhoBar 13077 BstLean.Part154.csC)) ≤ 1.50607E-7 := by
  have hr0 : 0 ≤ rhoBar 13077 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13077 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13077 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13077 BstLean.Part154.csC) (piBar (rhoBar 13077 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13077 BstLean.Part154.csC) (piBar (rhoBar 13077 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13077 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186747330 : ℝ) ^ 2 + 0.000118828618 ^ 2 + 3 * 0.000068980987 ^ 2 +
        2 * 0.797885 * 0.000186747330 * 0.000118828618 + 2 * 0.000186747330 * 0.000068980987 +
        4 * 0.797885 * 0.000118828618 * 0.000068980987 := by gcongr
    _ ≤ (1.50607E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13077 BstLean.Part154.csC Θ ≤ 0.002550904160 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13077 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13077 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13077 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13077 BstLean.Part154.csC) (piBar (rhoBar 13077 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13077 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035284762963 * 1.50607E-7 / (0.000244495477 : ℝ) := by gcongr
    _ ≤ 0.002550904160 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13077 BstLean.Part154.csC Θ ≤ 0.002828926707 + 0.000644572139 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13077 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13077 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13077 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035284762963 : ℝ) * ((2 * Θ * 0.000244495856 +
        (6863 / 10000) * 0.000244495856 * 13077 * 0.000978043203) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002828926707 + 0.000644572139 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13077 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13077 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13077 0.011 Θ ∧ gammaRatio 13077 0.011 Θ ≤ 0.000084051353 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13077 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035284762963 : ℝ) * 0.525 / ((1 - 0.011) * 13077) := by gcongr
      _ ≤ (0.000084051353 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13077 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13077 0.011 Θ) :=
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
    badAllowance 13077 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13077 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13077 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13077 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13077 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13077 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13077 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13077 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13077 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13077 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13077 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035284762963 : ℝ) * 13077 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13077 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003177179055 + 0.003195476299 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13077

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13077
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13077 BstLean.Part154.csC) (piBar (rhoBar 13077 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13077 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13077 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13077 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13077 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13077 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13077 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13077 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13077 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13077 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13077 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13077 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13077 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13077 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13077 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051714095102 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13077) ≤ 0.010443273979 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13077 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035284762963)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010443273979 + 2 * 0.737676 / 13077) := by gcongr
    _ ≤ (0.051714095102 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13077 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13077

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13077
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520125839 : ℝ) ≤ plow 13077 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13077) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052361404112)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339224684) : eMP 13077 0.011 xi bn ≤ 0.001153440204 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13077 : ℝ) * (1 - 0.011))) ≤ 0.000570360546 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001339224684 / (13077 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570360546 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570360546 : ℝ) + 3.141593 * 0.052361404112 / (13077 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001153440204 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052361404112)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339224684) : PiBarMP 13077 12 0.011 xi bn ≤ 0.158886508662 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13077 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036595418894 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.724021209241 : ℝ) ≤ √((13077 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.354711315275 : ℝ) ≤ √(13077 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13077) ≤ 0.121835017574 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036595418894 + 0.052361404112 * 1.772454 / (2 * (113.724021209241 : ℝ))) * (1 + 0.001153440204) +
        8 / (13077 * 114.354711315275) + 0.121835017574 := by gcongr
    _ ≤ (0.158886508662 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052361404112)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339224684) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280540238958) :
    parallelOracle 13077 0.011 xi bn cd ≤ 0.159848135074 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13077 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13077 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520125839 : ℝ) ≤ plow 13077 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.354711315275 : ℝ) ≤ √(13077 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280540238958 : ℝ) / (2 * 0.560520125839 * 114.354711315275)) * 0.158886508662 +
        0.280540238958 ^ 2 / (2 * 0.560520125839 * 114.354711315275) := by gcongr
    _ ≤ (0.159848135074 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052361404112) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339224684)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280540238958) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13077 13077 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520125839 : ℝ) ≤ plow 13077 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.354711315275 : ℝ) ≤ √(13077 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13077 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13077 Θ 1.22 ≤ 0.011596378363 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.354711315275 := by gcongr <;> linarith
      _ ≤ (0.011596378363 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13077 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13077 13077 0.011 ≤ 0.008358964071 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13077 13077 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13077 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13077 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13077 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13077 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159848135074 + 0.011596378363 + (0.008358964071 : ℝ) *
        (1 + 2 * (0.280540238958 + 0.011596378363) / (0.560520125839 * 114.354711315275))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13077]

end BstLean.Part269.N13077

/-! The original eight local profiles supply actual 13077 moment certificates. -/
namespace BstLean.Part269.N13077
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13077 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13077 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13077 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052361404112 ∧
    0 ≤ bN 13077 BstLean.Part154.csC (groupTheta g) ∧ bN 13077 BstLean.Part154.csC (groupTheta g) ≤ 0.001339224684 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13077 13077 0.011
      (momentAllowance 13077 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13077 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13077 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13077 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13077 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13077 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228826143856 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13077 0.011
      (momentAllowance 13077 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13077 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13077
/-! The actual computed-centre upper energy formula at 13077. -/
namespace BstLean.Part269.N13077
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13077

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13077
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13077)
open BstLean.Part268 (cell13077)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084460820111
  | 2 => 0.085386914039
  | 3 => 0.086308831736
  | 4 => 0.087227446852
  | 5 => 0.088143831828
  | 6 => 0.089059289343
  | 7 => 0.089975387107
  | 8 => 0.090893996074
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13077 13077 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13077 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13077

/-! Actual upper energy certificates on all 43 source endpoints at 13077. -/
namespace BstLean.Part269.N13077
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13077)
open BstLean.Part268 (cell13077)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13077 (gMinus 13077) (1 - (cell13077 i).lower) ≤ 1 ∧
    energyUpper 13077 (gMinus 13077) (BstLean.Part211.gPlus 13077)
      (finiteEnergy 13077 13077 0.011) (1 - (cell13077 i).lower) ≤
      (cell13077 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨10,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨11,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨12,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨13,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨14,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨15,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨16,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨17,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨18,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨19,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨20,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨21,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨22,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨23,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨24,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨25,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨26,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨27,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨28,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨29,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨30,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨31,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨32,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨33,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨34,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨35,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨36,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨37,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨38,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨39,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨40,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨41,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨42,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨43,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨44,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨45,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨46,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨47,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨48,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨49,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨50,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨51,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13077) (by norm_num)
        (q := 1 - (cell13077 ⟨52,by decide⟩).lower)
        (by norm_num [cell13077]) (by norm_num [cell13077])
      exact ⟨E.1,E.2.trans (by norm_num [cell13077])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13077

/-! Source-cell containment and simple scalar guards at 13077. -/
namespace BstLean.Part269.N13077
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13077)
open BstLean.Part268 (cell13077)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13077 ⟨10,by decide⟩).lower ∧ (cell13077 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13077 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13077 ⟨11,by decide⟩).lower ∧ (cell13077 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13077 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13077 ⟨12,by decide⟩).lower ∧ (cell13077 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13077 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13077 ⟨13,by decide⟩).lower ∧ (cell13077 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13077 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13077 ⟨14,by decide⟩).lower ∧ (cell13077 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13077 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13077 ⟨15,by decide⟩).lower ∧ (cell13077 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13077 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13077 ⟨16,by decide⟩).lower ∧ (cell13077 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13077 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13077 ⟨17,by decide⟩).lower ∧ (cell13077 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13077 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13077 ⟨18,by decide⟩).lower ∧ (cell13077 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13077 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13077 ⟨19,by decide⟩).lower ∧ (cell13077 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13077 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13077 ⟨20,by decide⟩).lower ∧ (cell13077 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13077 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13077 ⟨21,by decide⟩).lower ∧ (cell13077 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13077 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13077 ⟨22,by decide⟩).lower ∧ (cell13077 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13077 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13077 ⟨23,by decide⟩).lower ∧ (cell13077 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13077 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13077 ⟨24,by decide⟩).lower ∧ (cell13077 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13077 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13077 ⟨25,by decide⟩).lower ∧ (cell13077 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13077 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13077 ⟨26,by decide⟩).lower ∧ (cell13077 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13077 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13077 ⟨27,by decide⟩).lower ∧ (cell13077 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13077 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13077 ⟨28,by decide⟩).lower ∧ (cell13077 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13077 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13077 ⟨29,by decide⟩).lower ∧ (cell13077 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13077 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13077 ⟨30,by decide⟩).lower ∧ (cell13077 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13077 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13077 ⟨31,by decide⟩).lower ∧ (cell13077 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13077 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13077 ⟨32,by decide⟩).lower ∧ (cell13077 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13077 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13077 ⟨33,by decide⟩).lower ∧ (cell13077 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13077 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13077 ⟨34,by decide⟩).lower ∧ (cell13077 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13077 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13077 ⟨35,by decide⟩).lower ∧ (cell13077 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13077 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13077 ⟨36,by decide⟩).lower ∧ (cell13077 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13077 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13077 ⟨37,by decide⟩).lower ∧ (cell13077 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13077 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13077 ⟨38,by decide⟩).lower ∧ (cell13077 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13077 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13077 ⟨39,by decide⟩).lower ∧ (cell13077 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13077 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13077 ⟨40,by decide⟩).lower ∧ (cell13077 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13077 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13077 ⟨41,by decide⟩).lower ∧ (cell13077 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13077 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13077 ⟨42,by decide⟩).lower ∧ (cell13077 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13077 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13077 ⟨43,by decide⟩).lower ∧ (cell13077 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13077 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13077 ⟨44,by decide⟩).lower ∧ (cell13077 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13077 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13077 ⟨45,by decide⟩).lower ∧ (cell13077 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13077 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13077 ⟨46,by decide⟩).lower ∧ (cell13077 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13077 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13077 ⟨47,by decide⟩).lower ∧ (cell13077 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13077 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13077 ⟨48,by decide⟩).lower ∧ (cell13077 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13077 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13077 ⟨49,by decide⟩).lower ∧ (cell13077 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13077 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13077 ⟨50,by decide⟩).lower ∧ (cell13077 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13077 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13077 ⟨51,by decide⟩).lower ∧ (cell13077 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13077 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13077 ⟨52,by decide⟩).lower ∧ (cell13077 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13077 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13077 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13077 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13077,cell13077,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13077 i).lower ∧
    (cell13077 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13077 i).upper ≤ (0.532 : ℝ) ∧
    (cell13077 i).centre ≤ (0.1 : ℝ) ∧ (cell13077 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13077 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13077 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13077

/-! The local source numeric instances at 13077 have no network premises. -/
namespace BstLean.Part269.N13077
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13077)
open BstLean.Part268 (cell13077)

noncomputable def sourceNumerics13077 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13077 (cell13077 i)
      scalarRow13077.M scalarRow13077.H scalarRow13077.xi := by
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
    energy_allowance := scalarRow13077.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13077]
    centre_nonneg := (scalarRow13077.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13077])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13077
/-! Actual 13078 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13078
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13078 ≤ (1.035283402231 : ℝ) := by
  have hr : (114.359083591991 : ℝ) ≤ √(13078 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.359083591991 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13078 13078 (11 / 1000) ≤
    (0.008358644481 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13078) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.359083591991 : ℝ) ≤ √(13078 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13078)
  have hdiv : K / √(13078 : ℝ) ≤ K / 114.359083591991 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.359083591991 ≤ (0.008358644481 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13078.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13078 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13078 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13078 := gPlus_lower 13078
end BstLean.Part269.N13078

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13078
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035283402230 : ℝ) ≤ wn 13078 := by
  have hn : √(13078 : ℝ) ≤ 114.359083591992 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13078 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.359083591992 ≤ 2 / √(13078 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244476461 : ℝ) ≤ rhoBar 13078 BstLean.Part154.csC ∧
    rhoBar 13078 BstLean.Part154.csC ≤ 0.000244476839 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035283402230 : ℝ) / (1.295212 * 13078) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035283402231 : ℝ) / (1.29521 * 13078) := by gcongr
      _ ≤ (0.000244476839 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13078 BstLean.Part154.csC) ≤ 0.000977967125 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13078 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13078 BstLean.Part154.csC) (piBar (rhoBar 13078 BstLean.Part154.csC)) ≤ 0.000186732803 ∧
    cc1 (rhoBar 13078 BstLean.Part154.csC) (piBar (rhoBar 13078 BstLean.Part154.csC)) ≤ 0.000118819375 ∧
    cc2 (rhoBar 13078 BstLean.Part154.csC) ≤ 0.000068975622 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13078 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13078 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13078 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13078 BstLean.Part154.csC * nuR (rhoBar 13078 BstLean.Part154.csC)) ≤ 0.000488968621 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244476839 : ℝ) * 0.000977967125 := by gcongr
      _ ≤ (0.000488968621 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13078 BstLean.Part154.csC) * nuR (rhoBar 13078 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000977967125 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13078 BstLean.Part154.csC) * rhoBar 13078 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244476839 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244476839 / 2 + 0.399 * 0.000977967125 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186732803 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488968621 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118819375 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244476839 / 1.414213562 := by gcongr
      _ ≤ (0.000068975622 : ℝ) := by norm_num

end BstLean.Part269.N13078

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13078
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13078 BstLean.Part154.csC) (piBar (rhoBar 13078 BstLean.Part154.csC)) ≤ 1.50583E-7 := by
  have hr0 : 0 ≤ rhoBar 13078 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13078 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13078 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13078 BstLean.Part154.csC) (piBar (rhoBar 13078 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13078 BstLean.Part154.csC) (piBar (rhoBar 13078 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13078 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186732803 : ℝ) ^ 2 + 0.000118819375 ^ 2 + 3 * 0.000068975622 ^ 2 +
        2 * 0.797885 * 0.000186732803 * 0.000118819375 + 2 * 0.000186732803 * 0.000068975622 +
        4 * 0.797885 * 0.000118819375 * 0.000068975622 := by gcongr
    _ ≤ (1.50583E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13078 BstLean.Part154.csC Θ ≤ 0.002550692692 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13078 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13078 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13078 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13078 BstLean.Part154.csC) (piBar (rhoBar 13078 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13078 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035283402231 * 1.50583E-7 / (0.000244476461 : ℝ) := by gcongr
    _ ≤ 0.002550692692 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13078 BstLean.Part154.csC Θ ≤ 0.002828699215 + 0.000644521157 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13078 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13078 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13078 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035283402231 : ℝ) * ((2 * Θ * 0.000244476839 +
        (6863 / 10000) * 0.000244476839 * 13078 * 0.000977967125) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002828699215 + 0.000644521157 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13078 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13078 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13078 0.011 Θ ∧ gammaRatio 13078 0.011 Θ ≤ 0.000084044816 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13078 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035283402231 : ℝ) * 0.525 / ((1 - 0.011) * 13078) := by gcongr
      _ ≤ (0.000084044816 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13078 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13078 0.011 Θ) :=
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
    badAllowance 13078 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13078 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13078 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13078 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13078 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13078 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13078 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13078 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13078 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13078 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13078 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035283402231 : ℝ) * 13078 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13078 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003176951563 + 0.003195213849 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13078

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13078
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13078 BstLean.Part154.csC) (piBar (rhoBar 13078 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13078 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13078 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13078 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13078 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13078 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13078 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13078 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13078 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13078 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13078 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13078 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13078 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13078 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13078 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051712096795 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13078) ≤ 0.010442874703 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13078 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035283402231)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010442874703 + 2 * 0.737676 / 13078) := by gcongr
    _ ≤ (0.051712096795 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13078 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13078

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13078
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520168489 : ℝ) ≤ plow 13078 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13078) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052361038834)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339113664) : eMP 13078 0.011 xi bn ≤ 0.001153348247 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13078 : ℝ) * (1 - 0.011))) ≤ 0.000570315098 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001339113664 / (13078 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570315098 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570315098 : ℝ) + 3.141593 * 0.052361038834 / (13078 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001153348247 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052361038834)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339113664) : PiBarMP 13078 12 0.011 xi bn ≤ 0.158880309437 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13078 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036593902006 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.728369371938 : ℝ) ≤ √((13078 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.359083591991 : ℝ) ≤ √(13078 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13078) ≤ 0.121830359471 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036593902006 + 0.052361038834 * 1.772454 / (2 * (113.728369371938 : ℝ))) * (1 + 0.001153348247) +
        8 / (13078 * 114.359083591991) + 0.121830359471 := by gcongr
    _ ≤ (0.158880309437 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052361038834)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339113664) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280537442494) :
    parallelOracle 13078 0.011 xi bn cd ≤ 0.159841869740 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13078 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13078 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520168489 : ℝ) ≤ plow 13078 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.359083591991 : ℝ) ≤ √(13078 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280537442494 : ℝ) / (2 * 0.560520168489 * 114.359083591991)) * 0.158880309437 +
        0.280537442494 ^ 2 / (2 * 0.560520168489 * 114.359083591991) := by gcongr
    _ ≤ (0.159841869740 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052361038834) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339113664)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280537442494) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13078 13078 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520168489 : ℝ) ≤ plow 13078 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.359083591991 : ℝ) ≤ √(13078 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13078 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13078 Θ 1.22 ≤ 0.011595935001 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.359083591991 := by gcongr <;> linarith
      _ ≤ (0.011595935001 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13078 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13078 13078 0.011 ≤ 0.008358644481 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13078 13078 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13078 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13078 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13078 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13078 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159841869740 + 0.011595935001 + (0.008358644481 : ℝ) *
        (1 + 2 * (0.280537442494 + 0.011595935001) / (0.560520168489 * 114.359083591991))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13078]

end BstLean.Part269.N13078

/-! The original eight local profiles supply actual 13078 moment certificates. -/
namespace BstLean.Part269.N13078
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13078 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13078 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13078 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052361038834 ∧
    0 ≤ bN 13078 BstLean.Part154.csC (groupTheta g) ∧ bN 13078 BstLean.Part154.csC (groupTheta g) ≤ 0.001339113664 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13078 13078 0.011
      (momentAllowance 13078 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13078 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13078 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13078 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13078 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13078 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228825345699 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13078 0.011
      (momentAllowance 13078 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13078 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13078
/-! The actual computed-centre upper energy formula at 13078. -/
namespace BstLean.Part269.N13078
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13078

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13078
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13078)
open BstLean.Part268 (cell13078)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084458261913
  | 2 => 0.085384323383
  | 3 => 0.086306203871
  | 4 => 0.087224775901
  | 5 => 0.088141110578
  | 6 => 0.089056509017
  | 7 => 0.089972537091
  | 8 => 0.090891063624
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13078 13078 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13078 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13078

/-! Actual upper energy certificates on all 43 source endpoints at 13078. -/
namespace BstLean.Part269.N13078
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13078)
open BstLean.Part268 (cell13078)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13078 (gMinus 13078) (1 - (cell13078 i).lower) ≤ 1 ∧
    energyUpper 13078 (gMinus 13078) (BstLean.Part211.gPlus 13078)
      (finiteEnergy 13078 13078 0.011) (1 - (cell13078 i).lower) ≤
      (cell13078 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨10,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨11,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨12,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨13,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨14,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨15,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨16,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨17,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨18,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨19,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨20,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨21,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨22,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨23,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨24,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨25,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨26,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨27,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨28,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨29,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨30,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨31,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨32,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨33,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨34,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨35,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨36,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨37,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨38,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨39,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨40,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨41,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨42,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨43,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨44,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨45,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨46,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨47,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨48,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨49,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨50,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨51,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13078) (by norm_num)
        (q := 1 - (cell13078 ⟨52,by decide⟩).lower)
        (by norm_num [cell13078]) (by norm_num [cell13078])
      exact ⟨E.1,E.2.trans (by norm_num [cell13078])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13078

/-! Source-cell containment and simple scalar guards at 13078. -/
namespace BstLean.Part269.N13078
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13078)
open BstLean.Part268 (cell13078)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13078 ⟨10,by decide⟩).lower ∧ (cell13078 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13078 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13078 ⟨11,by decide⟩).lower ∧ (cell13078 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13078 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13078 ⟨12,by decide⟩).lower ∧ (cell13078 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13078 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13078 ⟨13,by decide⟩).lower ∧ (cell13078 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13078 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13078 ⟨14,by decide⟩).lower ∧ (cell13078 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13078 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13078 ⟨15,by decide⟩).lower ∧ (cell13078 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13078 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13078 ⟨16,by decide⟩).lower ∧ (cell13078 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13078 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13078 ⟨17,by decide⟩).lower ∧ (cell13078 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13078 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13078 ⟨18,by decide⟩).lower ∧ (cell13078 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13078 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13078 ⟨19,by decide⟩).lower ∧ (cell13078 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13078 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13078 ⟨20,by decide⟩).lower ∧ (cell13078 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13078 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13078 ⟨21,by decide⟩).lower ∧ (cell13078 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13078 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13078 ⟨22,by decide⟩).lower ∧ (cell13078 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13078 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13078 ⟨23,by decide⟩).lower ∧ (cell13078 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13078 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13078 ⟨24,by decide⟩).lower ∧ (cell13078 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13078 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13078 ⟨25,by decide⟩).lower ∧ (cell13078 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13078 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13078 ⟨26,by decide⟩).lower ∧ (cell13078 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13078 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13078 ⟨27,by decide⟩).lower ∧ (cell13078 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13078 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13078 ⟨28,by decide⟩).lower ∧ (cell13078 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13078 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13078 ⟨29,by decide⟩).lower ∧ (cell13078 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13078 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13078 ⟨30,by decide⟩).lower ∧ (cell13078 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13078 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13078 ⟨31,by decide⟩).lower ∧ (cell13078 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13078 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13078 ⟨32,by decide⟩).lower ∧ (cell13078 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13078 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13078 ⟨33,by decide⟩).lower ∧ (cell13078 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13078 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13078 ⟨34,by decide⟩).lower ∧ (cell13078 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13078 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13078 ⟨35,by decide⟩).lower ∧ (cell13078 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13078 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13078 ⟨36,by decide⟩).lower ∧ (cell13078 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13078 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13078 ⟨37,by decide⟩).lower ∧ (cell13078 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13078 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13078 ⟨38,by decide⟩).lower ∧ (cell13078 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13078 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13078 ⟨39,by decide⟩).lower ∧ (cell13078 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13078 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13078 ⟨40,by decide⟩).lower ∧ (cell13078 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13078 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13078 ⟨41,by decide⟩).lower ∧ (cell13078 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13078 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13078 ⟨42,by decide⟩).lower ∧ (cell13078 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13078 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13078 ⟨43,by decide⟩).lower ∧ (cell13078 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13078 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13078 ⟨44,by decide⟩).lower ∧ (cell13078 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13078 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13078 ⟨45,by decide⟩).lower ∧ (cell13078 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13078 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13078 ⟨46,by decide⟩).lower ∧ (cell13078 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13078 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13078 ⟨47,by decide⟩).lower ∧ (cell13078 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13078 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13078 ⟨48,by decide⟩).lower ∧ (cell13078 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13078 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13078 ⟨49,by decide⟩).lower ∧ (cell13078 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13078 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13078 ⟨50,by decide⟩).lower ∧ (cell13078 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13078 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13078 ⟨51,by decide⟩).lower ∧ (cell13078 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13078 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13078 ⟨52,by decide⟩).lower ∧ (cell13078 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13078 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13078 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13078 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13078,cell13078,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13078 i).lower ∧
    (cell13078 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13078 i).upper ≤ (0.532 : ℝ) ∧
    (cell13078 i).centre ≤ (0.1 : ℝ) ∧ (cell13078 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13078 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13078 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13078

/-! The local source numeric instances at 13078 have no network premises. -/
namespace BstLean.Part269.N13078
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13078)
open BstLean.Part268 (cell13078)

noncomputable def sourceNumerics13078 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13078 (cell13078 i)
      scalarRow13078.M scalarRow13078.H scalarRow13078.xi := by
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
    energy_allowance := scalarRow13078.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13078]
    centre_nonneg := (scalarRow13078.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13078])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13078
/-! Actual 13079 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13079
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13079 ≤ (1.035282041656 : ℝ) := by
  have hr : (114.363455701548 : ℝ) ≤ √(13079 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.363455701548 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13079 13079 (11 / 1000) ≤
    (0.008358324928 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13079) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.363455701548 : ℝ) ≤ √(13079 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13079)
  have hdiv : K / √(13079 : ℝ) ≤ K / 114.363455701548 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.363455701548 ≤ (0.008358324928 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13079.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13079 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13079 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13079 := gPlus_lower 13079
end BstLean.Part269.N13079

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13079
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035282041655 : ℝ) ≤ wn 13079 := by
  have hn : √(13079 : ℝ) ≤ 114.363455701549 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13079 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.363455701549 ≤ 2 / √(13079 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244457447 : ℝ) ≤ rhoBar 13079 BstLean.Part154.csC ∧
    rhoBar 13079 BstLean.Part154.csC ≤ 0.000244457825 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035282041655 : ℝ) / (1.295212 * 13079) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035282041656 : ℝ) / (1.29521 * 13079) := by gcongr
      _ ≤ (0.000244457825 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13079 BstLean.Part154.csC) ≤ 0.000977891060 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13079 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13079 BstLean.Part154.csC) (piBar (rhoBar 13079 BstLean.Part154.csC)) ≤ 0.000186718280 ∧
    cc1 (rhoBar 13079 BstLean.Part154.csC) (piBar (rhoBar 13079 BstLean.Part154.csC)) ≤ 0.000118810134 ∧
    cc2 (rhoBar 13079 BstLean.Part154.csC) ≤ 0.000068970257 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13079 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13079 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13079 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13079 BstLean.Part154.csC * nuR (rhoBar 13079 BstLean.Part154.csC)) ≤ 0.000488930590 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244457825 : ℝ) * 0.000977891060 := by gcongr
      _ ≤ (0.000488930590 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13079 BstLean.Part154.csC) * nuR (rhoBar 13079 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000977891060 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13079 BstLean.Part154.csC) * rhoBar 13079 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244457825 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244457825 / 2 + 0.399 * 0.000977891060 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186718280 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488930590 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118810134 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244457825 / 1.414213562 := by gcongr
      _ ≤ (0.000068970257 : ℝ) := by norm_num

end BstLean.Part269.N13079

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13079
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13079 BstLean.Part154.csC) (piBar (rhoBar 13079 BstLean.Part154.csC)) ≤ 1.50560E-7 := by
  have hr0 : 0 ≤ rhoBar 13079 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13079 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13079 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13079 BstLean.Part154.csC) (piBar (rhoBar 13079 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13079 BstLean.Part154.csC) (piBar (rhoBar 13079 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13079 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186718280 : ℝ) ^ 2 + 0.000118810134 ^ 2 + 3 * 0.000068970257 ^ 2 +
        2 * 0.797885 * 0.000186718280 * 0.000118810134 + 2 * 0.000186718280 * 0.000068970257 +
        4 * 0.797885 * 0.000118810134 * 0.000068970257 := by gcongr
    _ ≤ (1.50560E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13079 BstLean.Part154.csC Θ ≤ 0.002550498111 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13079 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13079 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13079 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13079 BstLean.Part154.csC) (piBar (rhoBar 13079 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13079 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035282041656 * 1.50560E-7 / (0.000244457447 : ℝ) := by gcongr
    _ ≤ 0.002550498111 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13079 BstLean.Part154.csC Θ ≤ 0.002828471764 + 0.000644470183 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13079 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13079 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13079 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035282041656 : ℝ) * ((2 * Θ * 0.000244457825 +
        (6863 / 10000) * 0.000244457825 * 13079 * 0.000977891060) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002828471764 + 0.000644470183 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13079 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13079 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13079 0.011 Θ ∧ gammaRatio 13079 0.011 Θ ≤ 0.000084038279 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13079 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035282041656 : ℝ) * 0.525 / ((1 - 0.011) * 13079) := by gcongr
      _ ≤ (0.000084038279 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13079 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13079 0.011 Θ) :=
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
    badAllowance 13079 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13079 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13079 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13079 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13079 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13079 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13079 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13079 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13079 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13079 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13079 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035282041656 : ℝ) * 13079 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13079 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003176724112 + 0.003194968294 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13079

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13079
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13079 BstLean.Part154.csC) (piBar (rhoBar 13079 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13079 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13079 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13079 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13079 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13079 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13079 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13079 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13079 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13079 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13079 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13079 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13079 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13079 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13079 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051710098715 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13079) ≤ 0.010442475472 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13079 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035282041656)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010442475472 + 2 * 0.737676 / 13079) := by gcongr
    _ ≤ (0.051710098715 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13079 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13079

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13079
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520211132 : ℝ) ≤ plow 13079 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13079) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052360682467)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339011509) : eMP 13079 0.011 xi bn ≤ 0.001153260076 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13079 : ℝ) * (1 - 0.011))) ≤ 0.000570271542 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001339011509 / (13079 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570271542 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570271542 : ℝ) + 3.141593 * 0.052360682467 / (13079 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001153260076 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052360682467)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339011509) : PiBarMP 13079 12 0.011 xi bn ≤ 0.158874232167 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13079 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036592506187 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.732717368398 : ℝ) ≤ √((13079 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.363455701548 : ℝ) ≤ √(13079 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13079) ≤ 0.121825701902 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036592506187 + 0.052360682467 * 1.772454 / (2 * (113.732717368398 : ℝ))) * (1 + 0.001153260076) +
        8 / (13079 * 114.363455701548) + 0.121825701902 := by gcongr
    _ ≤ (0.158874232167 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052360682467)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339011509) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280534665725) :
    parallelOracle 13079 0.011 xi bn cd ≤ 0.159835726745 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13079 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13079 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520211132 : ℝ) ≤ plow 13079 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.363455701548 : ℝ) ≤ √(13079 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280534665725 : ℝ) / (2 * 0.560520211132 * 114.363455701548)) * 0.158874232167 +
        0.280534665725 ^ 2 / (2 * 0.560520211132 * 114.363455701548) := by gcongr
    _ ≤ (0.159835726745 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052360682467) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001339011509)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280534665725) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13079 13079 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520211132 : ℝ) ≤ plow 13079 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.363455701548 : ℝ) ≤ √(13079 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13079 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13079 Θ 1.22 ≤ 0.011595491689 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.363455701548 := by gcongr <;> linarith
      _ ≤ (0.011595491689 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13079 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13079 13079 0.011 ≤ 0.008358324928 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13079 13079 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13079 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13079 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13079 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13079 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159835726745 + 0.011595491689 + (0.008358324928 : ℝ) *
        (1 + 2 * (0.280534665725 + 0.011595491689) / (0.560520211132 * 114.363455701548))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13079]

end BstLean.Part269.N13079

/-! The original eight local profiles supply actual 13079 moment certificates. -/
namespace BstLean.Part269.N13079
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13079 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13079 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13079 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052360682467 ∧
    0 ≤ bN 13079 BstLean.Part154.csC (groupTheta g) ∧ bN 13079 BstLean.Part154.csC (groupTheta g) ≤ 0.001339011509 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13079 13079 0.011
      (momentAllowance 13079 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13079 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13079 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13079 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13079 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13079 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228824567010 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13079 0.011
      (momentAllowance 13079 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13079 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13079
/-! The actual computed-centre upper energy formula at 13079. -/
namespace BstLean.Part269.N13079
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13079

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13079
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13079)
open BstLean.Part268 (cell13079)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084455704467
  | 2 => 0.085381733506
  | 3 => 0.086303576816
  | 4 => 0.087222105798
  | 5 => 0.088138390227
  | 6 => 0.089053729648
  | 7 => 0.089969688104
  | 8 => 0.090888132292
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13079 13079 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13079 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13079

/-! Actual upper energy certificates on all 43 source endpoints at 13079. -/
namespace BstLean.Part269.N13079
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13079)
open BstLean.Part268 (cell13079)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13079 (gMinus 13079) (1 - (cell13079 i).lower) ≤ 1 ∧
    energyUpper 13079 (gMinus 13079) (BstLean.Part211.gPlus 13079)
      (finiteEnergy 13079 13079 0.011) (1 - (cell13079 i).lower) ≤
      (cell13079 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨10,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨11,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨12,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨13,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨14,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨15,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨16,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨17,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨18,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨19,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨20,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨21,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨22,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨23,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨24,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨25,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨26,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨27,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨28,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨29,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨30,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨31,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨32,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨33,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨34,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨35,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨36,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨37,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨38,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨39,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨40,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨41,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨42,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨43,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨44,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨45,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨46,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨47,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨48,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨49,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨50,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨51,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13079) (by norm_num)
        (q := 1 - (cell13079 ⟨52,by decide⟩).lower)
        (by norm_num [cell13079]) (by norm_num [cell13079])
      exact ⟨E.1,E.2.trans (by norm_num [cell13079])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13079

/-! Source-cell containment and simple scalar guards at 13079. -/
namespace BstLean.Part269.N13079
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13079)
open BstLean.Part268 (cell13079)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13079 ⟨10,by decide⟩).lower ∧ (cell13079 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13079 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13079 ⟨11,by decide⟩).lower ∧ (cell13079 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13079 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13079 ⟨12,by decide⟩).lower ∧ (cell13079 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13079 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13079 ⟨13,by decide⟩).lower ∧ (cell13079 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13079 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13079 ⟨14,by decide⟩).lower ∧ (cell13079 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13079 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13079 ⟨15,by decide⟩).lower ∧ (cell13079 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13079 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13079 ⟨16,by decide⟩).lower ∧ (cell13079 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13079 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13079 ⟨17,by decide⟩).lower ∧ (cell13079 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13079 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13079 ⟨18,by decide⟩).lower ∧ (cell13079 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13079 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13079 ⟨19,by decide⟩).lower ∧ (cell13079 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13079 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13079 ⟨20,by decide⟩).lower ∧ (cell13079 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13079 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13079 ⟨21,by decide⟩).lower ∧ (cell13079 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13079 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13079 ⟨22,by decide⟩).lower ∧ (cell13079 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13079 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13079 ⟨23,by decide⟩).lower ∧ (cell13079 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13079 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13079 ⟨24,by decide⟩).lower ∧ (cell13079 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13079 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13079 ⟨25,by decide⟩).lower ∧ (cell13079 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13079 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13079 ⟨26,by decide⟩).lower ∧ (cell13079 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13079 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13079 ⟨27,by decide⟩).lower ∧ (cell13079 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13079 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13079 ⟨28,by decide⟩).lower ∧ (cell13079 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13079 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13079 ⟨29,by decide⟩).lower ∧ (cell13079 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13079 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13079 ⟨30,by decide⟩).lower ∧ (cell13079 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13079 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13079 ⟨31,by decide⟩).lower ∧ (cell13079 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13079 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13079 ⟨32,by decide⟩).lower ∧ (cell13079 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13079 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13079 ⟨33,by decide⟩).lower ∧ (cell13079 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13079 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13079 ⟨34,by decide⟩).lower ∧ (cell13079 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13079 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13079 ⟨35,by decide⟩).lower ∧ (cell13079 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13079 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13079 ⟨36,by decide⟩).lower ∧ (cell13079 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13079 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13079 ⟨37,by decide⟩).lower ∧ (cell13079 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13079 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13079 ⟨38,by decide⟩).lower ∧ (cell13079 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13079 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13079 ⟨39,by decide⟩).lower ∧ (cell13079 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13079 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13079 ⟨40,by decide⟩).lower ∧ (cell13079 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13079 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13079 ⟨41,by decide⟩).lower ∧ (cell13079 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13079 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13079 ⟨42,by decide⟩).lower ∧ (cell13079 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13079 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13079 ⟨43,by decide⟩).lower ∧ (cell13079 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13079 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13079 ⟨44,by decide⟩).lower ∧ (cell13079 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13079 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13079 ⟨45,by decide⟩).lower ∧ (cell13079 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13079 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13079 ⟨46,by decide⟩).lower ∧ (cell13079 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13079 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13079 ⟨47,by decide⟩).lower ∧ (cell13079 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13079 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13079 ⟨48,by decide⟩).lower ∧ (cell13079 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13079 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13079 ⟨49,by decide⟩).lower ∧ (cell13079 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13079 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13079 ⟨50,by decide⟩).lower ∧ (cell13079 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13079 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13079 ⟨51,by decide⟩).lower ∧ (cell13079 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13079 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13079 ⟨52,by decide⟩).lower ∧ (cell13079 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13079 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13079 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13079 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13079,cell13079,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13079 i).lower ∧
    (cell13079 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13079 i).upper ≤ (0.532 : ℝ) ∧
    (cell13079 i).centre ≤ (0.1 : ℝ) ∧ (cell13079 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13079 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13079 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13079

/-! The local source numeric instances at 13079 have no network premises. -/
namespace BstLean.Part269.N13079
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13079)
open BstLean.Part268 (cell13079)

noncomputable def sourceNumerics13079 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13079 (cell13079 i)
      scalarRow13079.M scalarRow13079.H scalarRow13079.xi := by
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
    energy_allowance := scalarRow13079.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13079]
    centre_nonneg := (scalarRow13079.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13079])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13079
/-! Actual 13080 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13080
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13080 ≤ (1.035280681237 : ℝ) := by
  have hr : (114.367827643966 : ℝ) ≤ √(13080 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.367827643966 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13080 13080 (11 / 1000) ≤
    (0.008358005412 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13080) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.367827643966 : ℝ) ≤ √(13080 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13080)
  have hdiv : K / √(13080 : ℝ) ≤ K / 114.367827643966 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.367827643966 ≤ (0.008358005412 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13080.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13080 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13080 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13080 := gPlus_lower 13080
end BstLean.Part269.N13080

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13080
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035280681236 : ℝ) ≤ wn 13080 := by
  have hn : √(13080 : ℝ) ≤ 114.367827643967 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13080 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.367827643967 ≤ 2 / √(13080 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244438436 : ℝ) ≤ rhoBar 13080 BstLean.Part154.csC ∧
    rhoBar 13080 BstLean.Part154.csC ≤ 0.000244438815 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035280681236 : ℝ) / (1.295212 * 13080) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035280681237 : ℝ) / (1.29521 * 13080) := by gcongr
      _ ≤ (0.000244438815 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13080 BstLean.Part154.csC) ≤ 0.000977815011 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13080 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13080 BstLean.Part154.csC) (piBar (rhoBar 13080 BstLean.Part154.csC)) ≤ 0.000186703759 ∧
    cc1 (rhoBar 13080 BstLean.Part154.csC) (piBar (rhoBar 13080 BstLean.Part154.csC)) ≤ 0.000118800895 ∧
    cc2 (rhoBar 13080 BstLean.Part154.csC) ≤ 0.000068964894 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13080 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13080 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13080 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13080 BstLean.Part154.csC * nuR (rhoBar 13080 BstLean.Part154.csC)) ≤ 0.000488892568 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244438815 : ℝ) * 0.000977815011 := by gcongr
      _ ≤ (0.000488892568 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13080 BstLean.Part154.csC) * nuR (rhoBar 13080 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000977815011 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13080 BstLean.Part154.csC) * rhoBar 13080 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244438815 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244438815 / 2 + 0.399 * 0.000977815011 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186703759 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488892568 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118800895 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244438815 / 1.414213562 := by gcongr
      _ ≤ (0.000068964894 : ℝ) := by norm_num

end BstLean.Part269.N13080

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13080
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13080 BstLean.Part154.csC) (piBar (rhoBar 13080 BstLean.Part154.csC)) ≤ 1.50537E-7 := by
  have hr0 : 0 ≤ rhoBar 13080 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13080 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13080 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13080 BstLean.Part154.csC) (piBar (rhoBar 13080 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13080 BstLean.Part154.csC) (piBar (rhoBar 13080 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13080 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186703759 : ℝ) ^ 2 + 0.000118800895 ^ 2 + 3 * 0.000068964894 ^ 2 +
        2 * 0.797885 * 0.000186703759 * 0.000118800895 + 2 * 0.000186703759 * 0.000068964894 +
        4 * 0.797885 * 0.000118800895 * 0.000068964894 := by gcongr
    _ ≤ (1.50537E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13080 BstLean.Part154.csC Θ ≤ 0.002550303471 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13080 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13080 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13080 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13080 BstLean.Part154.csC) (piBar (rhoBar 13080 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13080 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035280681237 * 1.50537E-7 / (0.000244438436 : ℝ) := by gcongr
    _ ≤ 0.002550303471 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13080 BstLean.Part154.csC Θ ≤ 0.002828244373 + 0.000644419220 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13080 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13080 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13080 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035280681237 : ℝ) * ((2 * Θ * 0.000244438815 +
        (6863 / 10000) * 0.000244438815 * 13080 * 0.000977815011) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002828244373 + 0.000644419220 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13080 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13080 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13080 0.011 Θ ∧ gammaRatio 13080 0.011 Θ ≤ 0.000084031744 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13080 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035280681237 : ℝ) * 0.525 / ((1 - 0.011) * 13080) := by gcongr
      _ ≤ (0.000084031744 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13080 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13080 0.011 Θ) :=
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
    badAllowance 13080 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13080 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13080 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13080 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13080 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13080 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13080 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13080 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13080 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13080 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13080 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035280681237 : ℝ) * 13080 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13080 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003176496721 + 0.003194722691 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13080

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13080
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13080 BstLean.Part154.csC) (piBar (rhoBar 13080 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13080 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13080 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13080 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13080 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13080 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13080 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13080 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13080 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13080 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13080 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13080 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13080 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13080 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13080 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051708100871 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13080) ≤ 0.010442076288 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13080 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035280681237)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010442076288 + 2 * 0.737676 / 13080) := by gcongr
    _ ≤ (0.051708100871 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13080 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13080

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13080
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520253769 : ℝ) ≤ plow 13080 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13080) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052360326134)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338909323) : eMP 13080 0.011 xi bn ≤ 0.001153171899 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13080 : ℝ) * (1 - 0.011))) ≤ 0.000570227983 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001338909323 / (13080 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570227983 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570227983 : ℝ) + 3.141593 * 0.052360326134 / (13080 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001153171899 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052360326134)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338909323) : PiBarMP 13080 12 0.011 xi bn ≤ 0.158868154955 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13080 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036591109891 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.737065198641 : ℝ) ≤ √((13080 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.367827643966 : ℝ) ≤ √(13080 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13080) ≤ 0.121821044867 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036591109891 + 0.052360326134 * 1.772454 / (2 * (113.737065198641 : ℝ))) * (1 + 0.001153171899) +
        8 / (13080 * 114.367827643966) + 0.121821044867 := by gcongr
    _ ≤ (0.158868154955 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052360326134)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338909323) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280531889263) :
    parallelOracle 13080 0.011 xi bn cd ≤ 0.159829583817 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13080 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13080 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520253769 : ℝ) ≤ plow 13080 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.367827643966 : ℝ) ≤ √(13080 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280531889263 : ℝ) / (2 * 0.560520253769 * 114.367827643966)) * 0.158868154955 +
        0.280531889263 ^ 2 / (2 * 0.560520253769 * 114.367827643966) := by gcongr
    _ ≤ (0.159829583817 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052360326134) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338909323)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280531889263) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13080 13080 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520253769 : ℝ) ≤ plow 13080 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.367827643966 : ℝ) ≤ √(13080 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13080 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13080 Θ 1.22 ≤ 0.011595048427 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.367827643966 := by gcongr <;> linarith
      _ ≤ (0.011595048427 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13080 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13080 13080 0.011 ≤ 0.008358005412 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13080 13080 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13080 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13080 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13080 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13080 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159829583817 + 0.011595048427 + (0.008358005412 : ℝ) *
        (1 + 2 * (0.280531889263 + 0.011595048427) / (0.560520253769 * 114.367827643966))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13080]

end BstLean.Part269.N13080

/-! The original eight local profiles supply actual 13080 moment certificates. -/
namespace BstLean.Part269.N13080
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13080 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13080 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13080 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052360326134 ∧
    0 ≤ bN 13080 BstLean.Part154.csC (groupTheta g) ∧ bN 13080 BstLean.Part154.csC (groupTheta g) ≤ 0.001338909323 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13080 13080 0.011
      (momentAllowance 13080 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13080 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13080 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13080 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13080 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13080 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228823788392 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13080 0.011
      (momentAllowance 13080 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13080 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13080
/-! The actual computed-centre upper energy formula at 13080. -/
namespace BstLean.Part269.N13080
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13080

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13080
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13080)
open BstLean.Part268 (cell13080)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084453147772
  | 2 => 0.085379144406
  | 3 => 0.086300950571
  | 4 => 0.087219436545
  | 5 => 0.088135670773
  | 6 => 0.089050951236
  | 7 => 0.089966840146
  | 8 => 0.090885202075
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13080 13080 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13080 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13080

/-! Actual upper energy certificates on all 43 source endpoints at 13080. -/
namespace BstLean.Part269.N13080
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13080)
open BstLean.Part268 (cell13080)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13080 (gMinus 13080) (1 - (cell13080 i).lower) ≤ 1 ∧
    energyUpper 13080 (gMinus 13080) (BstLean.Part211.gPlus 13080)
      (finiteEnergy 13080 13080 0.011) (1 - (cell13080 i).lower) ≤
      (cell13080 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨10,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨11,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨12,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨13,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨14,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨15,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨16,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨17,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨18,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨19,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨20,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨21,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨22,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨23,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨24,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨25,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨26,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨27,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨28,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨29,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨30,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨31,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨32,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨33,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨34,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨35,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨36,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨37,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨38,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨39,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨40,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨41,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨42,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨43,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨44,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨45,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨46,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨47,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨48,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨49,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨50,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨51,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13080) (by norm_num)
        (q := 1 - (cell13080 ⟨52,by decide⟩).lower)
        (by norm_num [cell13080]) (by norm_num [cell13080])
      exact ⟨E.1,E.2.trans (by norm_num [cell13080])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13080

/-! Source-cell containment and simple scalar guards at 13080. -/
namespace BstLean.Part269.N13080
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13080)
open BstLean.Part268 (cell13080)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13080 ⟨10,by decide⟩).lower ∧ (cell13080 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13080 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13080 ⟨11,by decide⟩).lower ∧ (cell13080 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13080 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13080 ⟨12,by decide⟩).lower ∧ (cell13080 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13080 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13080 ⟨13,by decide⟩).lower ∧ (cell13080 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13080 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13080 ⟨14,by decide⟩).lower ∧ (cell13080 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13080 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13080 ⟨15,by decide⟩).lower ∧ (cell13080 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13080 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13080 ⟨16,by decide⟩).lower ∧ (cell13080 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13080 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13080 ⟨17,by decide⟩).lower ∧ (cell13080 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13080 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13080 ⟨18,by decide⟩).lower ∧ (cell13080 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13080 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13080 ⟨19,by decide⟩).lower ∧ (cell13080 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13080 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13080 ⟨20,by decide⟩).lower ∧ (cell13080 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13080 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13080 ⟨21,by decide⟩).lower ∧ (cell13080 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13080 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13080 ⟨22,by decide⟩).lower ∧ (cell13080 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13080 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13080 ⟨23,by decide⟩).lower ∧ (cell13080 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13080 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13080 ⟨24,by decide⟩).lower ∧ (cell13080 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13080 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13080 ⟨25,by decide⟩).lower ∧ (cell13080 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13080 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13080 ⟨26,by decide⟩).lower ∧ (cell13080 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13080 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13080 ⟨27,by decide⟩).lower ∧ (cell13080 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13080 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13080 ⟨28,by decide⟩).lower ∧ (cell13080 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13080 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13080 ⟨29,by decide⟩).lower ∧ (cell13080 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13080 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13080 ⟨30,by decide⟩).lower ∧ (cell13080 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13080 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13080 ⟨31,by decide⟩).lower ∧ (cell13080 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13080 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13080 ⟨32,by decide⟩).lower ∧ (cell13080 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13080 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13080 ⟨33,by decide⟩).lower ∧ (cell13080 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13080 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13080 ⟨34,by decide⟩).lower ∧ (cell13080 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13080 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13080 ⟨35,by decide⟩).lower ∧ (cell13080 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13080 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13080 ⟨36,by decide⟩).lower ∧ (cell13080 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13080 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13080 ⟨37,by decide⟩).lower ∧ (cell13080 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13080 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13080 ⟨38,by decide⟩).lower ∧ (cell13080 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13080 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13080 ⟨39,by decide⟩).lower ∧ (cell13080 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13080 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13080 ⟨40,by decide⟩).lower ∧ (cell13080 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13080 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13080 ⟨41,by decide⟩).lower ∧ (cell13080 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13080 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13080 ⟨42,by decide⟩).lower ∧ (cell13080 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13080 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13080 ⟨43,by decide⟩).lower ∧ (cell13080 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13080 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13080 ⟨44,by decide⟩).lower ∧ (cell13080 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13080 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13080 ⟨45,by decide⟩).lower ∧ (cell13080 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13080 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13080 ⟨46,by decide⟩).lower ∧ (cell13080 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13080 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13080 ⟨47,by decide⟩).lower ∧ (cell13080 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13080 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13080 ⟨48,by decide⟩).lower ∧ (cell13080 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13080 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13080 ⟨49,by decide⟩).lower ∧ (cell13080 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13080 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13080 ⟨50,by decide⟩).lower ∧ (cell13080 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13080 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13080 ⟨51,by decide⟩).lower ∧ (cell13080 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13080 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13080 ⟨52,by decide⟩).lower ∧ (cell13080 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13080 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13080 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13080 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13080,cell13080,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13080 i).lower ∧
    (cell13080 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13080 i).upper ≤ (0.532 : ℝ) ∧
    (cell13080 i).centre ≤ (0.1 : ℝ) ∧ (cell13080 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13080 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13080 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13080

/-! The local source numeric instances at 13080 have no network premises. -/
namespace BstLean.Part269.N13080
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13080)
open BstLean.Part268 (cell13080)

noncomputable def sourceNumerics13080 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13080 (cell13080 i)
      scalarRow13080.M scalarRow13080.H scalarRow13080.xi := by
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
    energy_allowance := scalarRow13080.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13080]
    centre_nonneg := (scalarRow13080.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13080])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13080
/-! Actual 13081 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13081
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13081 ≤ (1.035279320976 : ℝ) := by
  have hr : (114.372199419264 : ℝ) ≤ √(13081 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.372199419264 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13081 13081 (11 / 1000) ≤
    (0.008357685932 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13081) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.372199419264 : ℝ) ≤ √(13081 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13081)
  have hdiv : K / √(13081 : ℝ) ≤ K / 114.372199419264 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.372199419264 ≤ (0.008357685932 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13081.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13081 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13081 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13081 := gPlus_lower 13081
end BstLean.Part269.N13081

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13081
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035279320975 : ℝ) ≤ wn 13081 := by
  have hn : √(13081 : ℝ) ≤ 114.372199419265 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13081 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.372199419265 ≤ 2 / √(13081 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244419429 : ℝ) ≤ rhoBar 13081 BstLean.Part154.csC ∧
    rhoBar 13081 BstLean.Part154.csC ≤ 0.000244419807 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035279320975 : ℝ) / (1.295212 * 13081) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035279320976 : ℝ) / (1.29521 * 13081) := by gcongr
      _ ≤ (0.000244419807 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13081 BstLean.Part154.csC) ≤ 0.000977738970 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13081 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13081 BstLean.Part154.csC) (piBar (rhoBar 13081 BstLean.Part154.csC)) ≤ 0.000186689240 ∧
    cc1 (rhoBar 13081 BstLean.Part154.csC) (piBar (rhoBar 13081 BstLean.Part154.csC)) ≤ 0.000118791656 ∧
    cc2 (rhoBar 13081 BstLean.Part154.csC) ≤ 0.000068959531 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13081 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13081 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13081 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13081 BstLean.Part154.csC * nuR (rhoBar 13081 BstLean.Part154.csC)) ≤ 0.000488854550 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244419807 : ℝ) * 0.000977738970 := by gcongr
      _ ≤ (0.000488854550 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13081 BstLean.Part154.csC) * nuR (rhoBar 13081 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000977738970 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13081 BstLean.Part154.csC) * rhoBar 13081 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244419807 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244419807 / 2 + 0.399 * 0.000977738970 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186689240 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488854550 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118791656 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244419807 / 1.414213562 := by gcongr
      _ ≤ (0.000068959531 : ℝ) := by norm_num

end BstLean.Part269.N13081

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13081
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13081 BstLean.Part154.csC) (piBar (rhoBar 13081 BstLean.Part154.csC)) ≤ 1.50513E-7 := by
  have hr0 : 0 ≤ rhoBar 13081 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13081 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13081 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13081 BstLean.Part154.csC) (piBar (rhoBar 13081 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13081 BstLean.Part154.csC) (piBar (rhoBar 13081 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13081 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186689240 : ℝ) ^ 2 + 0.000118791656 ^ 2 + 3 * 0.000068959531 ^ 2 +
        2 * 0.797885 * 0.000186689240 * 0.000118791656 + 2 * 0.000186689240 * 0.000068959531 +
        4 * 0.797885 * 0.000118791656 * 0.000068959531 := by gcongr
    _ ≤ (1.50513E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13081 BstLean.Part154.csC Θ ≤ 0.002550091817 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13081 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13081 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13081 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13081 BstLean.Part154.csC) (piBar (rhoBar 13081 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13081 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035279320976 * 1.50513E-7 / (0.000244419429 : ℝ) := by gcongr
    _ ≤ 0.002550091817 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13081 BstLean.Part154.csC Θ ≤ 0.002828016996 + 0.000644368262 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13081 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13081 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13081 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035279320976 : ℝ) * ((2 * Θ * 0.000244419807 +
        (6863 / 10000) * 0.000244419807 * 13081 * 0.000977738970) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002828016996 + 0.000644368262 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13081 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13081 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13081 0.011 Θ ∧ gammaRatio 13081 0.011 Θ ≤ 0.000084025209 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13081 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035279320976 : ℝ) * 0.525 / ((1 - 0.011) * 13081) := by gcongr
      _ ≤ (0.000084025209 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13081 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13081 0.011 Θ) :=
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
    badAllowance 13081 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13081 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13081 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13081 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13081 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13081 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13081 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13081 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13081 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13081 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13081 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035279320976 : ℝ) * 13081 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13081 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003176269344 + 0.003194460079 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13081

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13081
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13081 BstLean.Part154.csC) (piBar (rhoBar 13081 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13081 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13081 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13081 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13081 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13081 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13081 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13081 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13081 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13081 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13081 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13081 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13081 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13081 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13081 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051706103254 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13081) ≤ 0.010441677149 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13081 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035279320976)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010441677149 + 2 * 0.737676 / 13081) := by gcongr
    _ ≤ (0.051706103254 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13081 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13081

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13081
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520296399 : ℝ) ≤ plow 13081 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13081) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052359960886)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338798204) : eMP 13081 0.011 xi bn ≤ 0.001153079923 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13081 : ℝ) * (1 - 0.011))) ≤ 0.000570182525 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001338798204 / (13081 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570182525 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570182525 : ℝ) + 3.141593 * 0.052359960886 / (13081 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001153079923 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052359960886)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338798204) : PiBarMP 13081 12 0.011 xi bn ≤ 0.158861955806 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13081 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036589591471 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.741412862686 : ℝ) ≤ √((13081 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.372199419264 : ℝ) ≤ √(13081 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13081) ≤ 0.121816388367 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036589591471 + 0.052359960886 * 1.772454 / (2 * (113.741412862686 : ℝ))) * (1 + 0.001153079923) +
        8 / (13081 * 114.372199419264) + 0.121816388367 := by gcongr
    _ ≤ (0.158861955806 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052359960886)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338798204) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280529093546) :
    parallelOracle 13081 0.011 xi bn cd ≤ 0.159823318584 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13081 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13081 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520296399 : ℝ) ≤ plow 13081 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.372199419264 : ℝ) ≤ √(13081 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280529093546 : ℝ) / (2 * 0.560520296399 * 114.372199419264)) * 0.158861955806 +
        0.280529093546 ^ 2 / (2 * 0.560520296399 * 114.372199419264) := by gcongr
    _ ≤ (0.159823318584 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052359960886) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338798204)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280529093546) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13081 13081 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520296399 : ℝ) ≤ plow 13081 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.372199419264 : ℝ) ≤ √(13081 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13081 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13081 Θ 1.22 ≤ 0.011594605217 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.372199419264 := by gcongr <;> linarith
      _ ≤ (0.011594605217 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13081 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13081 13081 0.011 ≤ 0.008357685932 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13081 13081 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13081 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13081 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13081 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13081 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159823318584 + 0.011594605217 + (0.008357685932 : ℝ) *
        (1 + 2 * (0.280529093546 + 0.011594605217) / (0.560520296399 * 114.372199419264))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13081]

end BstLean.Part269.N13081

/-! The original eight local profiles supply actual 13081 moment certificates. -/
namespace BstLean.Part269.N13081
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13081 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13081 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13081 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052359960886 ∧
    0 ≤ bN 13081 BstLean.Part154.csC (groupTheta g) ∧ bN 13081 BstLean.Part154.csC (groupTheta g) ≤ 0.001338798204 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13081 13081 0.011
      (momentAllowance 13081 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13081 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13081 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13081 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13081 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13081 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228822990292 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13081 0.011
      (momentAllowance 13081 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13081 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13081
/-! The actual computed-centre upper energy formula at 13081. -/
namespace BstLean.Part269.N13081
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13081

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13081
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13081)
open BstLean.Part268 (cell13081)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084450591829
  | 2 => 0.085376556083
  | 3 => 0.086298325134
  | 4 => 0.087216768140
  | 5 => 0.088132952216
  | 6 => 0.089048173779
  | 7 => 0.089963993216
  | 8 => 0.090882272973
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13081 13081 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13081 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13081

/-! Actual upper energy certificates on all 43 source endpoints at 13081. -/
namespace BstLean.Part269.N13081
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13081)
open BstLean.Part268 (cell13081)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13081 (gMinus 13081) (1 - (cell13081 i).lower) ≤ 1 ∧
    energyUpper 13081 (gMinus 13081) (BstLean.Part211.gPlus 13081)
      (finiteEnergy 13081 13081 0.011) (1 - (cell13081 i).lower) ≤
      (cell13081 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨10,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨11,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨12,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨13,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨14,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨15,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨16,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨17,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨18,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨19,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨20,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨21,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨22,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨23,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨24,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨25,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨26,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨27,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨28,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨29,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨30,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨31,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨32,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨33,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨34,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨35,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨36,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨37,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨38,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨39,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨40,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨41,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨42,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨43,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨44,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨45,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨46,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨47,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨48,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨49,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨50,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨51,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13081) (by norm_num)
        (q := 1 - (cell13081 ⟨52,by decide⟩).lower)
        (by norm_num [cell13081]) (by norm_num [cell13081])
      exact ⟨E.1,E.2.trans (by norm_num [cell13081])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13081

/-! Source-cell containment and simple scalar guards at 13081. -/
namespace BstLean.Part269.N13081
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13081)
open BstLean.Part268 (cell13081)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13081 ⟨10,by decide⟩).lower ∧ (cell13081 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13081 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13081 ⟨11,by decide⟩).lower ∧ (cell13081 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13081 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13081 ⟨12,by decide⟩).lower ∧ (cell13081 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13081 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13081 ⟨13,by decide⟩).lower ∧ (cell13081 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13081 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13081 ⟨14,by decide⟩).lower ∧ (cell13081 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13081 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13081 ⟨15,by decide⟩).lower ∧ (cell13081 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13081 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13081 ⟨16,by decide⟩).lower ∧ (cell13081 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13081 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13081 ⟨17,by decide⟩).lower ∧ (cell13081 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13081 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13081 ⟨18,by decide⟩).lower ∧ (cell13081 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13081 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13081 ⟨19,by decide⟩).lower ∧ (cell13081 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13081 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13081 ⟨20,by decide⟩).lower ∧ (cell13081 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13081 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13081 ⟨21,by decide⟩).lower ∧ (cell13081 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13081 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13081 ⟨22,by decide⟩).lower ∧ (cell13081 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13081 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13081 ⟨23,by decide⟩).lower ∧ (cell13081 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13081 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13081 ⟨24,by decide⟩).lower ∧ (cell13081 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13081 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13081 ⟨25,by decide⟩).lower ∧ (cell13081 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13081 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13081 ⟨26,by decide⟩).lower ∧ (cell13081 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13081 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13081 ⟨27,by decide⟩).lower ∧ (cell13081 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13081 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13081 ⟨28,by decide⟩).lower ∧ (cell13081 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13081 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13081 ⟨29,by decide⟩).lower ∧ (cell13081 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13081 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13081 ⟨30,by decide⟩).lower ∧ (cell13081 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13081 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13081 ⟨31,by decide⟩).lower ∧ (cell13081 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13081 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13081 ⟨32,by decide⟩).lower ∧ (cell13081 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13081 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13081 ⟨33,by decide⟩).lower ∧ (cell13081 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13081 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13081 ⟨34,by decide⟩).lower ∧ (cell13081 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13081 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13081 ⟨35,by decide⟩).lower ∧ (cell13081 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13081 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13081 ⟨36,by decide⟩).lower ∧ (cell13081 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13081 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13081 ⟨37,by decide⟩).lower ∧ (cell13081 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13081 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13081 ⟨38,by decide⟩).lower ∧ (cell13081 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13081 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13081 ⟨39,by decide⟩).lower ∧ (cell13081 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13081 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13081 ⟨40,by decide⟩).lower ∧ (cell13081 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13081 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13081 ⟨41,by decide⟩).lower ∧ (cell13081 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13081 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13081 ⟨42,by decide⟩).lower ∧ (cell13081 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13081 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13081 ⟨43,by decide⟩).lower ∧ (cell13081 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13081 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13081 ⟨44,by decide⟩).lower ∧ (cell13081 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13081 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13081 ⟨45,by decide⟩).lower ∧ (cell13081 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13081 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13081 ⟨46,by decide⟩).lower ∧ (cell13081 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13081 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13081 ⟨47,by decide⟩).lower ∧ (cell13081 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13081 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13081 ⟨48,by decide⟩).lower ∧ (cell13081 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13081 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13081 ⟨49,by decide⟩).lower ∧ (cell13081 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13081 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13081 ⟨50,by decide⟩).lower ∧ (cell13081 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13081 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13081 ⟨51,by decide⟩).lower ∧ (cell13081 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13081 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13081 ⟨52,by decide⟩).lower ∧ (cell13081 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13081 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13081 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13081 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13081,cell13081,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13081 i).lower ∧
    (cell13081 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13081 i).upper ≤ (0.532 : ℝ) ∧
    (cell13081 i).centre ≤ (0.1 : ℝ) ∧ (cell13081 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13081 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13081 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13081

/-! The local source numeric instances at 13081 have no network premises. -/
namespace BstLean.Part269.N13081
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13081)
open BstLean.Part268 (cell13081)

noncomputable def sourceNumerics13081 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13081 (cell13081 i)
      scalarRow13081.M scalarRow13081.H scalarRow13081.xi := by
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
    energy_allowance := scalarRow13081.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13081]
    centre_nonneg := (scalarRow13081.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13081])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13081
/-! Actual 13082 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13082
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13082 ≤ (1.035277960871 : ℝ) := by
  have hr : (114.376571027461 : ℝ) ≤ √(13082 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.376571027461 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13082 13082 (11 / 1000) ≤
    (0.008357366489 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13082) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.376571027461 : ℝ) ≤ √(13082 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13082)
  have hdiv : K / √(13082 : ℝ) ≤ K / 114.376571027461 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.376571027461 ≤ (0.008357366489 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13082.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13082 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13082 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13082 := gPlus_lower 13082
end BstLean.Part269.N13082

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13082
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035277960870 : ℝ) ≤ wn 13082 := by
  have hn : √(13082 : ℝ) ≤ 114.376571027462 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13082 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.376571027462 ≤ 2 / √(13082 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244400424 : ℝ) ≤ rhoBar 13082 BstLean.Part154.csC ∧
    rhoBar 13082 BstLean.Part154.csC ≤ 0.000244400802 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035277960870 : ℝ) / (1.295212 * 13082) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035277960871 : ℝ) / (1.29521 * 13082) := by gcongr
      _ ≤ (0.000244400802 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13082 BstLean.Part154.csC) ≤ 0.000977662940 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13082 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13082 BstLean.Part154.csC) (piBar (rhoBar 13082 BstLean.Part154.csC)) ≤ 0.000186674723 ∧
    cc1 (rhoBar 13082 BstLean.Part154.csC) (piBar (rhoBar 13082 BstLean.Part154.csC)) ≤ 0.000118782419 ∧
    cc2 (rhoBar 13082 BstLean.Part154.csC) ≤ 0.000068954169 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13082 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13082 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13082 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13082 BstLean.Part154.csC * nuR (rhoBar 13082 BstLean.Part154.csC)) ≤ 0.000488816537 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244400802 : ℝ) * 0.000977662940 := by gcongr
      _ ≤ (0.000488816537 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13082 BstLean.Part154.csC) * nuR (rhoBar 13082 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000977662940 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13082 BstLean.Part154.csC) * rhoBar 13082 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244400802 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244400802 / 2 + 0.399 * 0.000977662940 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186674723 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488816537 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118782419 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244400802 / 1.414213562 := by gcongr
      _ ≤ (0.000068954169 : ℝ) := by norm_num

end BstLean.Part269.N13082

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13082
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13082 BstLean.Part154.csC) (piBar (rhoBar 13082 BstLean.Part154.csC)) ≤ 1.50490E-7 := by
  have hr0 : 0 ≤ rhoBar 13082 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13082 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13082 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13082 BstLean.Part154.csC) (piBar (rhoBar 13082 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13082 BstLean.Part154.csC) (piBar (rhoBar 13082 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13082 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186674723 : ℝ) ^ 2 + 0.000118782419 ^ 2 + 3 * 0.000068954169 ^ 2 +
        2 * 0.797885 * 0.000186674723 * 0.000118782419 + 2 * 0.000186674723 * 0.000068954169 +
        4 * 0.797885 * 0.000118782419 * 0.000068954169 := by gcongr
    _ ≤ (1.50490E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13082 BstLean.Part154.csC Θ ≤ 0.002549897055 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13082 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13082 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13082 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13082 BstLean.Part154.csC) (piBar (rhoBar 13082 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13082 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035277960871 * 1.50490E-7 / (0.000244400424 : ℝ) := by gcongr
    _ ≤ 0.002549897055 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13082 BstLean.Part154.csC Θ ≤ 0.002827789653 + 0.000644317312 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13082 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13082 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13082 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035277960871 : ℝ) * ((2 * Θ * 0.000244400802 +
        (6863 / 10000) * 0.000244400802 * 13082 * 0.000977662940) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002827789653 + 0.000644317312 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13082 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13082 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13082 0.011 Θ ∧ gammaRatio 13082 0.011 Θ ≤ 0.000084018676 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13082 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035277960871 : ℝ) * 0.525 / ((1 - 0.011) * 13082) := by gcongr
      _ ≤ (0.000084018676 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13082 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13082 0.011 Θ) :=
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
    badAllowance 13082 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13082 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13082 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13082 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13082 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13082 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13082 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13082 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13082 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13082 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13082 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035277960871 : ℝ) * 13082 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13082 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003176042001 + 0.003194214367 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13082

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13082
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13082 BstLean.Part154.csC) (piBar (rhoBar 13082 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13082 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13082 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13082 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13082 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13082 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13082 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13082 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13082 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13082 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13082 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13082 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13082 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13082 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13082 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051704105864 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13082) ≤ 0.010441278055 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13082 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035277960871)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010441278055 + 2 * 0.737676 / 13082) := by gcongr
    _ ≤ (0.051704105864 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13082 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13082

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13082
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520339023 : ℝ) ≤ plow 13082 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13082) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052359604544)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338695954) : eMP 13082 0.011 xi bn ≤ 0.001152991730 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13082 : ℝ) * (1 - 0.011))) ≤ 0.000570138958 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001338695954 / (13082 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570138958 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570138958 : ℝ) + 3.141593 * 0.052359604544 / (13082 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001152991730 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052359604544)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338695954) : PiBarMP 13082 12 0.011 xi bn ≤ 0.158855878679 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13082 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036588194189 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.745760360551 : ℝ) ≤ √((13082 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.376571027461 : ℝ) ≤ √(13082 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13082) ≤ 0.121811732400 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036588194189 + 0.052359604544 * 1.772454 / (2 * (113.745760360551 : ℝ))) * (1 + 0.001152991730) +
        8 / (13082 * 114.376571027461) + 0.121811732400 := by gcongr
    _ ≤ (0.158855878679 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052359604544)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338695954) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280526317514) :
    parallelOracle 13082 0.011 xi bn cd ≤ 0.159817175757 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13082 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13082 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520339023 : ℝ) ≤ plow 13082 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.376571027461 : ℝ) ≤ √(13082 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280526317514 : ℝ) / (2 * 0.560520339023 * 114.376571027461)) * 0.158855878679 +
        0.280526317514 ^ 2 / (2 * 0.560520339023 * 114.376571027461) := by gcongr
    _ ≤ (0.159817175757 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052359604544) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338695954)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280526317514) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13082 13082 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520339023 : ℝ) ≤ plow 13082 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.376571027461 : ℝ) ≤ √(13082 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13082 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13082 Θ 1.22 ≤ 0.011594162057 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.376571027461 := by gcongr <;> linarith
      _ ≤ (0.011594162057 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13082 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13082 13082 0.011 ≤ 0.008357366489 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13082 13082 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13082 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13082 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13082 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13082 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159817175757 + 0.011594162057 + (0.008357366489 : ℝ) *
        (1 + 2 * (0.280526317514 + 0.011594162057) / (0.560520339023 * 114.376571027461))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13082]

end BstLean.Part269.N13082

/-! The original eight local profiles supply actual 13082 moment certificates. -/
namespace BstLean.Part269.N13082
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13082 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13082 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13082 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052359604544 ∧
    0 ≤ bN 13082 BstLean.Part154.csC (groupTheta g) ∧ bN 13082 BstLean.Part154.csC (groupTheta g) ≤ 0.001338695954 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13082 13082 0.011
      (momentAllowance 13082 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13082 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13082 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13082 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13082 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13082 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228822211650 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13082 0.011
      (momentAllowance 13082 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13082 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13082
/-! The actual computed-centre upper energy formula at 13082. -/
namespace BstLean.Part269.N13082
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13082

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13082
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13082)
open BstLean.Part268 (cell13082)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084448036635
  | 2 => 0.085373968535
  | 3 => 0.086295700505
  | 4 => 0.087214100582
  | 5 => 0.088130234554
  | 6 => 0.089045397277
  | 7 => 0.089961147312
  | 8 => 0.090879344985
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13082 13082 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13082 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13082

/-! Actual upper energy certificates on all 43 source endpoints at 13082. -/
namespace BstLean.Part269.N13082
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13082)
open BstLean.Part268 (cell13082)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13082 (gMinus 13082) (1 - (cell13082 i).lower) ≤ 1 ∧
    energyUpper 13082 (gMinus 13082) (BstLean.Part211.gPlus 13082)
      (finiteEnergy 13082 13082 0.011) (1 - (cell13082 i).lower) ≤
      (cell13082 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨10,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨11,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨12,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨13,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨14,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨15,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨16,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨17,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨18,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨19,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨20,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨21,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨22,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨23,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨24,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨25,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨26,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨27,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨28,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨29,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨30,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨31,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨32,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨33,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨34,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨35,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨36,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨37,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨38,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨39,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨40,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨41,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨42,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨43,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨44,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨45,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨46,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨47,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨48,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨49,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨50,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨51,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13082) (by norm_num)
        (q := 1 - (cell13082 ⟨52,by decide⟩).lower)
        (by norm_num [cell13082]) (by norm_num [cell13082])
      exact ⟨E.1,E.2.trans (by norm_num [cell13082])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13082

/-! Source-cell containment and simple scalar guards at 13082. -/
namespace BstLean.Part269.N13082
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13082)
open BstLean.Part268 (cell13082)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13082 ⟨10,by decide⟩).lower ∧ (cell13082 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13082 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13082 ⟨11,by decide⟩).lower ∧ (cell13082 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13082 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13082 ⟨12,by decide⟩).lower ∧ (cell13082 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13082 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13082 ⟨13,by decide⟩).lower ∧ (cell13082 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13082 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13082 ⟨14,by decide⟩).lower ∧ (cell13082 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13082 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13082 ⟨15,by decide⟩).lower ∧ (cell13082 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13082 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13082 ⟨16,by decide⟩).lower ∧ (cell13082 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13082 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13082 ⟨17,by decide⟩).lower ∧ (cell13082 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13082 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13082 ⟨18,by decide⟩).lower ∧ (cell13082 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13082 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13082 ⟨19,by decide⟩).lower ∧ (cell13082 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13082 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13082 ⟨20,by decide⟩).lower ∧ (cell13082 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13082 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13082 ⟨21,by decide⟩).lower ∧ (cell13082 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13082 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13082 ⟨22,by decide⟩).lower ∧ (cell13082 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13082 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13082 ⟨23,by decide⟩).lower ∧ (cell13082 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13082 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13082 ⟨24,by decide⟩).lower ∧ (cell13082 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13082 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13082 ⟨25,by decide⟩).lower ∧ (cell13082 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13082 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13082 ⟨26,by decide⟩).lower ∧ (cell13082 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13082 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13082 ⟨27,by decide⟩).lower ∧ (cell13082 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13082 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13082 ⟨28,by decide⟩).lower ∧ (cell13082 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13082 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13082 ⟨29,by decide⟩).lower ∧ (cell13082 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13082 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13082 ⟨30,by decide⟩).lower ∧ (cell13082 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13082 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13082 ⟨31,by decide⟩).lower ∧ (cell13082 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13082 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13082 ⟨32,by decide⟩).lower ∧ (cell13082 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13082 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13082 ⟨33,by decide⟩).lower ∧ (cell13082 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13082 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13082 ⟨34,by decide⟩).lower ∧ (cell13082 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13082 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13082 ⟨35,by decide⟩).lower ∧ (cell13082 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13082 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13082 ⟨36,by decide⟩).lower ∧ (cell13082 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13082 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13082 ⟨37,by decide⟩).lower ∧ (cell13082 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13082 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13082 ⟨38,by decide⟩).lower ∧ (cell13082 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13082 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13082 ⟨39,by decide⟩).lower ∧ (cell13082 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13082 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13082 ⟨40,by decide⟩).lower ∧ (cell13082 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13082 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13082 ⟨41,by decide⟩).lower ∧ (cell13082 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13082 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13082 ⟨42,by decide⟩).lower ∧ (cell13082 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13082 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13082 ⟨43,by decide⟩).lower ∧ (cell13082 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13082 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13082 ⟨44,by decide⟩).lower ∧ (cell13082 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13082 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13082 ⟨45,by decide⟩).lower ∧ (cell13082 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13082 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13082 ⟨46,by decide⟩).lower ∧ (cell13082 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13082 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13082 ⟨47,by decide⟩).lower ∧ (cell13082 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13082 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13082 ⟨48,by decide⟩).lower ∧ (cell13082 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13082 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13082 ⟨49,by decide⟩).lower ∧ (cell13082 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13082 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13082 ⟨50,by decide⟩).lower ∧ (cell13082 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13082 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13082 ⟨51,by decide⟩).lower ∧ (cell13082 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13082 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13082 ⟨52,by decide⟩).lower ∧ (cell13082 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13082 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13082 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13082 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13082,cell13082,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13082 i).lower ∧
    (cell13082 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13082 i).upper ≤ (0.532 : ℝ) ∧
    (cell13082 i).centre ≤ (0.1 : ℝ) ∧ (cell13082 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13082 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13082 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13082

/-! The local source numeric instances at 13082 have no network premises. -/
namespace BstLean.Part269.N13082
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13082)
open BstLean.Part268 (cell13082)

noncomputable def sourceNumerics13082 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13082 (cell13082 i)
      scalarRow13082.M scalarRow13082.H scalarRow13082.xi := by
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
    energy_allowance := scalarRow13082.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13082]
    centre_nonneg := (scalarRow13082.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13082])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13082
/-! Actual 13083 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13083
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13083 ≤ (1.035276600923 : ℝ) := by
  have hr : (114.380942468577 : ℝ) ≤ √(13083 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.380942468577 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13083 13083 (11 / 1000) ≤
    (0.008357047082 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13083) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.380942468577 : ℝ) ≤ √(13083 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13083)
  have hdiv : K / √(13083 : ℝ) ≤ K / 114.380942468577 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.380942468577 ≤ (0.008357047082 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13083.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13083 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13083 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13083 := gPlus_lower 13083
end BstLean.Part269.N13083

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13083
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035276600922 : ℝ) ≤ wn 13083 := by
  have hn : √(13083 : ℝ) ≤ 114.380942468578 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13083 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.380942468578 ≤ 2 / √(13083 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244381422 : ℝ) ≤ rhoBar 13083 BstLean.Part154.csC ∧
    rhoBar 13083 BstLean.Part154.csC ≤ 0.000244381801 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035276600922 : ℝ) / (1.295212 * 13083) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035276600923 : ℝ) / (1.29521 * 13083) := by gcongr
      _ ≤ (0.000244381801 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13083 BstLean.Part154.csC) ≤ 0.000977586927 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13083 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13083 BstLean.Part154.csC) (piBar (rhoBar 13083 BstLean.Part154.csC)) ≤ 0.000186660210 ∧
    cc1 (rhoBar 13083 BstLean.Part154.csC) (piBar (rhoBar 13083 BstLean.Part154.csC)) ≤ 0.000118773184 ∧
    cc2 (rhoBar 13083 BstLean.Part154.csC) ≤ 0.000068948808 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13083 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13083 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13083 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13083 BstLean.Part154.csC * nuR (rhoBar 13083 BstLean.Part154.csC)) ≤ 0.000488778533 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244381801 : ℝ) * 0.000977586927 := by gcongr
      _ ≤ (0.000488778533 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13083 BstLean.Part154.csC) * nuR (rhoBar 13083 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000977586927 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13083 BstLean.Part154.csC) * rhoBar 13083 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244381801 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244381801 / 2 + 0.399 * 0.000977586927 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186660210 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488778533 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118773184 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244381801 / 1.414213562 := by gcongr
      _ ≤ (0.000068948808 : ℝ) := by norm_num

end BstLean.Part269.N13083

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13083
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13083 BstLean.Part154.csC) (piBar (rhoBar 13083 BstLean.Part154.csC)) ≤ 1.50466E-7 := by
  have hr0 : 0 ≤ rhoBar 13083 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13083 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13083 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13083 BstLean.Part154.csC) (piBar (rhoBar 13083 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13083 BstLean.Part154.csC) (piBar (rhoBar 13083 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13083 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186660210 : ℝ) ^ 2 + 0.000118773184 ^ 2 + 3 * 0.000068948808 ^ 2 +
        2 * 0.797885 * 0.000186660210 * 0.000118773184 + 2 * 0.000186660210 * 0.000068948808 +
        4 * 0.797885 * 0.000118773184 * 0.000068948808 := by gcongr
    _ ≤ (1.50466E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13083 BstLean.Part154.csC Θ ≤ 0.002549685288 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13083 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13083 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13083 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13083 BstLean.Part154.csC) (piBar (rhoBar 13083 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13083 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035276600923 * 1.50466E-7 / (0.000244381422 : ℝ) := by gcongr
    _ ≤ 0.002549685288 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13083 BstLean.Part154.csC Θ ≤ 0.002827562374 + 0.000644266373 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13083 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13083 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13083 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035276600923 : ℝ) * ((2 * Θ * 0.000244381801 +
        (6863 / 10000) * 0.000244381801 * 13083 * 0.000977586927) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002827562374 + 0.000644266373 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13083 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13083 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13083 0.011 Θ ∧ gammaRatio 13083 0.011 Θ ≤ 0.000084012144 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13083 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035276600923 : ℝ) * 0.525 / ((1 - 0.011) * 13083) := by gcongr
      _ ≤ (0.000084012144 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13083 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13083 0.011 Θ) :=
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
    badAllowance 13083 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13083 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13083 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13083 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13083 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13083 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13083 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13083 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13083 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13083 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13083 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035276600923 : ℝ) * 13083 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13083 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003175814722 + 0.003193951661 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13083

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13083
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13083 BstLean.Part154.csC) (piBar (rhoBar 13083 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13083 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13083 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13083 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13083 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13083 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13083 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13083 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13083 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13083 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13083 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13083 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13083 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13083 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13083 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051702108711 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13083) ≤ 0.010440879008 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13083 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035276600923)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010440879008 + 2 * 0.737676 / 13083) := by gcongr
    _ ≤ (0.051702108711 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13083 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13083

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13083
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520381640 : ℝ) ≤ plow 13083 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13083) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052359239345)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338584777) : eMP 13083 0.011 xi bn ≤ 0.001152899742 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13083 : ℝ) * (1 - 0.011))) ≤ 0.000570093494 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001338584777 / (13083 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570093494 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570093494 : ℝ) + 3.141593 * 0.052359239345 / (13083 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001152899742 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052359239345)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338584777) : PiBarMP 13083 12 0.011 xi bn ≤ 0.158849679688 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13083 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036586674856 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.750107692256 : ℝ) ≤ √((13083 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.380942468577 : ℝ) ≤ √(13083 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13083) ≤ 0.121807076967 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036586674856 + 0.052359239345 * 1.772454 / (2 * (113.750107692256 : ℝ))) * (1 + 0.001152899742) +
        8 / (13083 * 114.380942468577) + 0.121807076967 := by gcongr
    _ ≤ (0.158849679688 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052359239345)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338584777) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280523522362) :
    parallelOracle 13083 0.011 xi bn cd ≤ 0.159810910699 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13083 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13083 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520381640 : ℝ) ≤ plow 13083 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.380942468577 : ℝ) ≤ √(13083 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280523522362 : ℝ) / (2 * 0.560520381640 * 114.380942468577)) * 0.158849679688 +
        0.280523522362 ^ 2 / (2 * 0.560520381640 * 114.380942468577) := by gcongr
    _ ≤ (0.159810910699 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052359239345) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338584777)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280523522362) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13083 13083 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520381640 : ℝ) ≤ plow 13083 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.380942468577 : ℝ) ≤ √(13083 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13083 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13083 Θ 1.22 ≤ 0.011593718949 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.380942468577 := by gcongr <;> linarith
      _ ≤ (0.011593718949 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13083 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13083 13083 0.011 ≤ 0.008357047082 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13083 13083 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13083 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13083 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13083 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13083 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159810910699 + 0.011593718949 + (0.008357047082 : ℝ) *
        (1 + 2 * (0.280523522362 + 0.011593718949) / (0.560520381640 * 114.380942468577))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13083]

end BstLean.Part269.N13083

/-! The original eight local profiles supply actual 13083 moment certificates. -/
namespace BstLean.Part269.N13083
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13083 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13083 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13083 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052359239345 ∧
    0 ≤ bN 13083 BstLean.Part154.csC (groupTheta g) ∧ bN 13083 BstLean.Part154.csC (groupTheta g) ≤ 0.001338584777 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13083 13083 0.011
      (momentAllowance 13083 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13083 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13083 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13083 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13083 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13083 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228821413651 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13083 0.011
      (momentAllowance 13083 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13083 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13083
/-! The actual computed-centre upper energy formula at 13083. -/
namespace BstLean.Part269.N13083
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13083

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13083
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13083)
open BstLean.Part268 (cell13083)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084445482191
  | 2 => 0.085371381762
  | 3 => 0.086293076683
  | 4 => 0.087211433870
  | 5 => 0.088127517786
  | 6 => 0.089042621729
  | 7 => 0.089958302434
  | 8 => 0.090876418109
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13083 13083 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13083 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13083

/-! Actual upper energy certificates on all 43 source endpoints at 13083. -/
namespace BstLean.Part269.N13083
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13083)
open BstLean.Part268 (cell13083)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13083 (gMinus 13083) (1 - (cell13083 i).lower) ≤ 1 ∧
    energyUpper 13083 (gMinus 13083) (BstLean.Part211.gPlus 13083)
      (finiteEnergy 13083 13083 0.011) (1 - (cell13083 i).lower) ≤
      (cell13083 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨10,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨11,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨12,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨13,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨14,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨15,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨16,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨17,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨18,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨19,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨20,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨21,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨22,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨23,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨24,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨25,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨26,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨27,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨28,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨29,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨30,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨31,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨32,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨33,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨34,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨35,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨36,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨37,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨38,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨39,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨40,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨41,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨42,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨43,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨44,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨45,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨46,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨47,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨48,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨49,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨50,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨51,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13083) (by norm_num)
        (q := 1 - (cell13083 ⟨52,by decide⟩).lower)
        (by norm_num [cell13083]) (by norm_num [cell13083])
      exact ⟨E.1,E.2.trans (by norm_num [cell13083])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13083

/-! Source-cell containment and simple scalar guards at 13083. -/
namespace BstLean.Part269.N13083
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13083)
open BstLean.Part268 (cell13083)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13083 ⟨10,by decide⟩).lower ∧ (cell13083 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13083 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13083 ⟨11,by decide⟩).lower ∧ (cell13083 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13083 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13083 ⟨12,by decide⟩).lower ∧ (cell13083 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13083 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13083 ⟨13,by decide⟩).lower ∧ (cell13083 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13083 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13083 ⟨14,by decide⟩).lower ∧ (cell13083 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13083 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13083 ⟨15,by decide⟩).lower ∧ (cell13083 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13083 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13083 ⟨16,by decide⟩).lower ∧ (cell13083 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13083 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13083 ⟨17,by decide⟩).lower ∧ (cell13083 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13083 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13083 ⟨18,by decide⟩).lower ∧ (cell13083 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13083 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13083 ⟨19,by decide⟩).lower ∧ (cell13083 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13083 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13083 ⟨20,by decide⟩).lower ∧ (cell13083 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13083 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13083 ⟨21,by decide⟩).lower ∧ (cell13083 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13083 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13083 ⟨22,by decide⟩).lower ∧ (cell13083 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13083 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13083 ⟨23,by decide⟩).lower ∧ (cell13083 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13083 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13083 ⟨24,by decide⟩).lower ∧ (cell13083 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13083 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13083 ⟨25,by decide⟩).lower ∧ (cell13083 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13083 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13083 ⟨26,by decide⟩).lower ∧ (cell13083 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13083 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13083 ⟨27,by decide⟩).lower ∧ (cell13083 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13083 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13083 ⟨28,by decide⟩).lower ∧ (cell13083 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13083 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13083 ⟨29,by decide⟩).lower ∧ (cell13083 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13083 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13083 ⟨30,by decide⟩).lower ∧ (cell13083 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13083 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13083 ⟨31,by decide⟩).lower ∧ (cell13083 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13083 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13083 ⟨32,by decide⟩).lower ∧ (cell13083 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13083 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13083 ⟨33,by decide⟩).lower ∧ (cell13083 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13083 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13083 ⟨34,by decide⟩).lower ∧ (cell13083 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13083 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13083 ⟨35,by decide⟩).lower ∧ (cell13083 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13083 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13083 ⟨36,by decide⟩).lower ∧ (cell13083 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13083 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13083 ⟨37,by decide⟩).lower ∧ (cell13083 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13083 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13083 ⟨38,by decide⟩).lower ∧ (cell13083 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13083 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13083 ⟨39,by decide⟩).lower ∧ (cell13083 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13083 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13083 ⟨40,by decide⟩).lower ∧ (cell13083 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13083 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13083 ⟨41,by decide⟩).lower ∧ (cell13083 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13083 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13083 ⟨42,by decide⟩).lower ∧ (cell13083 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13083 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13083 ⟨43,by decide⟩).lower ∧ (cell13083 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13083 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13083 ⟨44,by decide⟩).lower ∧ (cell13083 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13083 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13083 ⟨45,by decide⟩).lower ∧ (cell13083 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13083 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13083 ⟨46,by decide⟩).lower ∧ (cell13083 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13083 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13083 ⟨47,by decide⟩).lower ∧ (cell13083 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13083 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13083 ⟨48,by decide⟩).lower ∧ (cell13083 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13083 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13083 ⟨49,by decide⟩).lower ∧ (cell13083 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13083 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13083 ⟨50,by decide⟩).lower ∧ (cell13083 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13083 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13083 ⟨51,by decide⟩).lower ∧ (cell13083 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13083 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13083 ⟨52,by decide⟩).lower ∧ (cell13083 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13083 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13083 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13083 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13083,cell13083,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13083 i).lower ∧
    (cell13083 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13083 i).upper ≤ (0.532 : ℝ) ∧
    (cell13083 i).centre ≤ (0.1 : ℝ) ∧ (cell13083 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13083 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13083 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13083

/-! The local source numeric instances at 13083 have no network premises. -/
namespace BstLean.Part269.N13083
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13083)
open BstLean.Part268 (cell13083)

noncomputable def sourceNumerics13083 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13083 (cell13083 i)
      scalarRow13083.M scalarRow13083.H scalarRow13083.xi := by
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
    energy_allowance := scalarRow13083.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13083]
    centre_nonneg := (scalarRow13083.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13083])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13083
/-! Actual 13084 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13084
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13084 ≤ (1.035275241132 : ℝ) := by
  have hr : (114.385313742630 : ℝ) ≤ √(13084 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.385313742630 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13084 13084 (11 / 1000) ≤
    (0.008356727713 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13084) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.385313742630 : ℝ) ≤ √(13084 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13084)
  have hdiv : K / √(13084 : ℝ) ≤ K / 114.385313742630 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.385313742630 ≤ (0.008356727713 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13084.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13084 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13084 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13084 := gPlus_lower 13084
end BstLean.Part269.N13084

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13084
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035275241131 : ℝ) ≤ wn 13084 := by
  have hn : √(13084 : ℝ) ≤ 114.385313742631 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13084 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.385313742631 ≤ 2 / √(13084 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244362423 : ℝ) ≤ rhoBar 13084 BstLean.Part154.csC ∧
    rhoBar 13084 BstLean.Part154.csC ≤ 0.000244362802 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035275241131 : ℝ) / (1.295212 * 13084) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035275241132 : ℝ) / (1.29521 * 13084) := by gcongr
      _ ≤ (0.000244362802 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13084 BstLean.Part154.csC) ≤ 0.000977510922 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13084 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13084 BstLean.Part154.csC) (piBar (rhoBar 13084 BstLean.Part154.csC)) ≤ 0.000186645698 ∧
    cc1 (rhoBar 13084 BstLean.Part154.csC) (piBar (rhoBar 13084 BstLean.Part154.csC)) ≤ 0.000118763950 ∧
    cc2 (rhoBar 13084 BstLean.Part154.csC) ≤ 0.000068943448 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13084 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13084 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13084 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13084 BstLean.Part154.csC * nuR (rhoBar 13084 BstLean.Part154.csC)) ≤ 0.000488740533 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244362802 : ℝ) * 0.000977510922 := by gcongr
      _ ≤ (0.000488740533 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13084 BstLean.Part154.csC) * nuR (rhoBar 13084 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000977510922 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13084 BstLean.Part154.csC) * rhoBar 13084 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244362802 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244362802 / 2 + 0.399 * 0.000977510922 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186645698 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488740533 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118763950 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244362802 / 1.414213562 := by gcongr
      _ ≤ (0.000068943448 : ℝ) := by norm_num

end BstLean.Part269.N13084

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13084
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13084 BstLean.Part154.csC) (piBar (rhoBar 13084 BstLean.Part154.csC)) ≤ 1.50443E-7 := by
  have hr0 : 0 ≤ rhoBar 13084 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13084 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13084 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13084 BstLean.Part154.csC) (piBar (rhoBar 13084 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13084 BstLean.Part154.csC) (piBar (rhoBar 13084 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13084 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186645698 : ℝ) ^ 2 + 0.000118763950 ^ 2 + 3 * 0.000068943448 ^ 2 +
        2 * 0.797885 * 0.000186645698 * 0.000118763950 + 2 * 0.000186645698 * 0.000068943448 +
        4 * 0.797885 * 0.000118763950 * 0.000068943448 := by gcongr
    _ ≤ (1.50443E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13084 BstLean.Part154.csC Θ ≤ 0.002549490404 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13084 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13084 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13084 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13084 BstLean.Part154.csC) (piBar (rhoBar 13084 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13084 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035275241132 * 1.50443E-7 / (0.000244362423 : ℝ) := by gcongr
    _ ≤ 0.002549490404 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13084 BstLean.Part154.csC Θ ≤ 0.002827335109 + 0.000644215440 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13084 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13084 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13084 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035275241132 : ℝ) * ((2 * Θ * 0.000244362802 +
        (6863 / 10000) * 0.000244362802 * 13084 * 0.000977510922) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002827335109 + 0.000644215440 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13084 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13084 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13084 0.011 Θ ∧ gammaRatio 13084 0.011 Θ ≤ 0.000084005612 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13084 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035275241132 : ℝ) * 0.525 / ((1 - 0.011) * 13084) := by gcongr
      _ ≤ (0.000084005612 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13084 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13084 0.011 Θ) :=
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
    badAllowance 13084 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13084 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13084 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13084 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13084 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13084 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13084 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13084 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13084 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13084 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13084 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035275241132 : ℝ) * 13084 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13084 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003175587457 + 0.003193705844 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13084

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13084
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13084 BstLean.Part154.csC) (piBar (rhoBar 13084 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13084 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13084 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13084 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13084 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13084 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13084 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13084 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13084 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13084 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13084 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13084 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13084 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13084 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13084 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051700111785 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13084) ≤ 0.010440480006 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13084 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035275241132)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010440480006 + 2 * 0.737676 / 13084) := by gcongr
    _ ≤ (0.051700111785 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13084 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13084

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13084
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520424250 : ℝ) ≤ plow 13084 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13084) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052358883026)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338482463) : eMP 13084 0.011 xi bn ≤ 0.001152811538 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13084 : ℝ) * (1 - 0.011))) ≤ 0.000570049921 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001338482463 / (13084 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570049921 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570049921 : ℝ) + 3.141593 * 0.052358883026 / (13084 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001152811538 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052358883026)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338482463) : PiBarMP 13084 12 0.011 xi bn ≤ 0.158843602647 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13084 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036585276588 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.754454857820 : ℝ) ≤ √((13084 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.385313742630 : ℝ) ≤ √(13084 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13084) ≤ 0.121802422068 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036585276588 + 0.052358883026 * 1.772454 / (2 * (113.754454857820 : ℝ))) * (1 + 0.001152811538) +
        8 / (13084 * 114.385313742630) + 0.121802422068 := by gcongr
    _ ≤ (0.158843602647 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052358883026)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338482463) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280520746838) :
    parallelOracle 13084 0.011 xi bn cd ≤ 0.159804767975 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13084 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13084 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520424250 : ℝ) ≤ plow 13084 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.385313742630 : ℝ) ≤ √(13084 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280520746838 : ℝ) / (2 * 0.560520424250 * 114.385313742630)) * 0.158843602647 +
        0.280520746838 ^ 2 / (2 * 0.560520424250 * 114.385313742630) := by gcongr
    _ ≤ (0.159804767975 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052358883026) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338482463)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280520746838) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13084 13084 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520424250 : ℝ) ≤ plow 13084 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.385313742630 : ℝ) ≤ √(13084 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13084 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13084 Θ 1.22 ≤ 0.011593275891 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.385313742630 := by gcongr <;> linarith
      _ ≤ (0.011593275891 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13084 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13084 13084 0.011 ≤ 0.008356727713 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13084 13084 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13084 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13084 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13084 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13084 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159804767975 + 0.011593275891 + (0.008356727713 : ℝ) *
        (1 + 2 * (0.280520746838 + 0.011593275891) / (0.560520424250 * 114.385313742630))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13084]

end BstLean.Part269.N13084

/-! The original eight local profiles supply actual 13084 moment certificates. -/
namespace BstLean.Part269.N13084
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13084 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13084 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13084 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052358883026 ∧
    0 ≤ bN 13084 BstLean.Part154.csC (groupTheta g) ∧ bN 13084 BstLean.Part154.csC (groupTheta g) ≤ 0.001338482463 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13084 13084 0.011
      (momentAllowance 13084 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13084 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13084 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13084 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13084 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13084 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228820635053 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13084 0.011
      (momentAllowance 13084 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13084 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13084
/-! The actual computed-centre upper energy formula at 13084. -/
namespace BstLean.Part269.N13084
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13084

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13084
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13084)
open BstLean.Part268 (cell13084)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084442928496
  | 2 => 0.085368795764
  | 3 => 0.086290453667
  | 4 => 0.087208768003
  | 5 => 0.088124801913
  | 6 => 0.089039847134
  | 7 => 0.089955458581
  | 8 => 0.090873492344
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13084 13084 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13084 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13084

/-! Actual upper energy certificates on all 43 source endpoints at 13084. -/
namespace BstLean.Part269.N13084
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13084)
open BstLean.Part268 (cell13084)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13084 (gMinus 13084) (1 - (cell13084 i).lower) ≤ 1 ∧
    energyUpper 13084 (gMinus 13084) (BstLean.Part211.gPlus 13084)
      (finiteEnergy 13084 13084 0.011) (1 - (cell13084 i).lower) ≤
      (cell13084 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨10,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨11,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨12,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨13,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨14,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨15,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨16,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨17,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨18,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨19,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨20,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨21,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨22,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨23,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨24,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨25,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨26,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨27,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨28,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨29,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨30,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨31,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨32,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨33,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨34,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨35,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨36,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨37,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨38,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨39,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨40,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨41,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨42,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨43,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨44,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨45,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨46,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨47,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨48,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨49,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨50,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨51,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13084) (by norm_num)
        (q := 1 - (cell13084 ⟨52,by decide⟩).lower)
        (by norm_num [cell13084]) (by norm_num [cell13084])
      exact ⟨E.1,E.2.trans (by norm_num [cell13084])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13084

/-! Source-cell containment and simple scalar guards at 13084. -/
namespace BstLean.Part269.N13084
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13084)
open BstLean.Part268 (cell13084)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13084 ⟨10,by decide⟩).lower ∧ (cell13084 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13084 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13084 ⟨11,by decide⟩).lower ∧ (cell13084 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13084 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13084 ⟨12,by decide⟩).lower ∧ (cell13084 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13084 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13084 ⟨13,by decide⟩).lower ∧ (cell13084 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13084 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13084 ⟨14,by decide⟩).lower ∧ (cell13084 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13084 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13084 ⟨15,by decide⟩).lower ∧ (cell13084 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13084 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13084 ⟨16,by decide⟩).lower ∧ (cell13084 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13084 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13084 ⟨17,by decide⟩).lower ∧ (cell13084 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13084 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13084 ⟨18,by decide⟩).lower ∧ (cell13084 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13084 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13084 ⟨19,by decide⟩).lower ∧ (cell13084 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13084 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13084 ⟨20,by decide⟩).lower ∧ (cell13084 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13084 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13084 ⟨21,by decide⟩).lower ∧ (cell13084 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13084 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13084 ⟨22,by decide⟩).lower ∧ (cell13084 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13084 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13084 ⟨23,by decide⟩).lower ∧ (cell13084 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13084 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13084 ⟨24,by decide⟩).lower ∧ (cell13084 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13084 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13084 ⟨25,by decide⟩).lower ∧ (cell13084 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13084 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13084 ⟨26,by decide⟩).lower ∧ (cell13084 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13084 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13084 ⟨27,by decide⟩).lower ∧ (cell13084 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13084 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13084 ⟨28,by decide⟩).lower ∧ (cell13084 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13084 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13084 ⟨29,by decide⟩).lower ∧ (cell13084 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13084 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13084 ⟨30,by decide⟩).lower ∧ (cell13084 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13084 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13084 ⟨31,by decide⟩).lower ∧ (cell13084 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13084 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13084 ⟨32,by decide⟩).lower ∧ (cell13084 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13084 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13084 ⟨33,by decide⟩).lower ∧ (cell13084 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13084 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13084 ⟨34,by decide⟩).lower ∧ (cell13084 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13084 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13084 ⟨35,by decide⟩).lower ∧ (cell13084 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13084 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13084 ⟨36,by decide⟩).lower ∧ (cell13084 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13084 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13084 ⟨37,by decide⟩).lower ∧ (cell13084 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13084 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13084 ⟨38,by decide⟩).lower ∧ (cell13084 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13084 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13084 ⟨39,by decide⟩).lower ∧ (cell13084 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13084 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13084 ⟨40,by decide⟩).lower ∧ (cell13084 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13084 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13084 ⟨41,by decide⟩).lower ∧ (cell13084 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13084 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13084 ⟨42,by decide⟩).lower ∧ (cell13084 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13084 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13084 ⟨43,by decide⟩).lower ∧ (cell13084 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13084 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13084 ⟨44,by decide⟩).lower ∧ (cell13084 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13084 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13084 ⟨45,by decide⟩).lower ∧ (cell13084 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13084 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13084 ⟨46,by decide⟩).lower ∧ (cell13084 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13084 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13084 ⟨47,by decide⟩).lower ∧ (cell13084 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13084 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13084 ⟨48,by decide⟩).lower ∧ (cell13084 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13084 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13084 ⟨49,by decide⟩).lower ∧ (cell13084 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13084 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13084 ⟨50,by decide⟩).lower ∧ (cell13084 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13084 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13084 ⟨51,by decide⟩).lower ∧ (cell13084 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13084 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13084 ⟨52,by decide⟩).lower ∧ (cell13084 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13084 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13084 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13084 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13084,cell13084,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13084 i).lower ∧
    (cell13084 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13084 i).upper ≤ (0.532 : ℝ) ∧
    (cell13084 i).centre ≤ (0.1 : ℝ) ∧ (cell13084 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13084 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13084 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13084

/-! The local source numeric instances at 13084 have no network premises. -/
namespace BstLean.Part269.N13084
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13084)
open BstLean.Part268 (cell13084)

noncomputable def sourceNumerics13084 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13084 (cell13084 i)
      scalarRow13084.M scalarRow13084.H scalarRow13084.xi := by
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
    energy_allowance := scalarRow13084.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13084]
    centre_nonneg := (scalarRow13084.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13084])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13084
/-! Actual 13085 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13085
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13085 ≤ (1.035273881498 : ℝ) := by
  have hr : (114.389684849640 : ℝ) ≤ √(13085 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.389684849640 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13085 13085 (11 / 1000) ≤
    (0.008356408379 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13085) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.389684849640 : ℝ) ≤ √(13085 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13085)
  have hdiv : K / √(13085 : ℝ) ≤ K / 114.389684849640 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.389684849640 ≤ (0.008356408379 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13085.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13085 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13085 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13085 := gPlus_lower 13085
end BstLean.Part269.N13085

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13085
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035273881497 : ℝ) ≤ wn 13085 := by
  have hn : √(13085 : ℝ) ≤ 114.389684849641 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13085 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.389684849641 ≤ 2 / √(13085 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244343427 : ℝ) ≤ rhoBar 13085 BstLean.Part154.csC ∧
    rhoBar 13085 BstLean.Part154.csC ≤ 0.000244343806 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035273881497 : ℝ) / (1.295212 * 13085) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035273881498 : ℝ) / (1.29521 * 13085) := by gcongr
      _ ≤ (0.000244343806 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13085 BstLean.Part154.csC) ≤ 0.000977434928 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13085 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13085 BstLean.Part154.csC) (piBar (rhoBar 13085 BstLean.Part154.csC)) ≤ 0.000186631188 ∧
    cc1 (rhoBar 13085 BstLean.Part154.csC) (piBar (rhoBar 13085 BstLean.Part154.csC)) ≤ 0.000118754717 ∧
    cc2 (rhoBar 13085 BstLean.Part154.csC) ≤ 0.000068938088 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13085 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13085 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13085 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13085 BstLean.Part154.csC * nuR (rhoBar 13085 BstLean.Part154.csC)) ≤ 0.000488702538 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244343806 : ℝ) * 0.000977434928 := by gcongr
      _ ≤ (0.000488702538 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13085 BstLean.Part154.csC) * nuR (rhoBar 13085 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000977434928 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13085 BstLean.Part154.csC) * rhoBar 13085 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244343806 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244343806 / 2 + 0.399 * 0.000977434928 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186631188 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488702538 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118754717 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244343806 / 1.414213562 := by gcongr
      _ ≤ (0.000068938088 : ℝ) := by norm_num

end BstLean.Part269.N13085

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13085
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13085 BstLean.Part154.csC) (piBar (rhoBar 13085 BstLean.Part154.csC)) ≤ 1.50420E-7 := by
  have hr0 : 0 ≤ rhoBar 13085 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13085 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13085 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13085 BstLean.Part154.csC) (piBar (rhoBar 13085 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13085 BstLean.Part154.csC) (piBar (rhoBar 13085 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13085 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186631188 : ℝ) ^ 2 + 0.000118754717 ^ 2 + 3 * 0.000068938088 ^ 2 +
        2 * 0.797885 * 0.000186631188 * 0.000118754717 + 2 * 0.000186631188 * 0.000068938088 +
        4 * 0.797885 * 0.000118754717 * 0.000068938088 := by gcongr
    _ ≤ (1.50420E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13085 BstLean.Part154.csC Θ ≤ 0.002549295460 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13085 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13085 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13085 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13085 BstLean.Part154.csC) (piBar (rhoBar 13085 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13085 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035273881498 * 1.50420E-7 / (0.000244343427 : ℝ) := by gcongr
    _ ≤ 0.002549295460 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13085 BstLean.Part154.csC Θ ≤ 0.002827107879 + 0.000644164514 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13085 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13085 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13085 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035273881498 : ℝ) * ((2 * Θ * 0.000244343806 +
        (6863 / 10000) * 0.000244343806 * 13085 * 0.000977434928) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002827107879 + 0.000644164514 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13085 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13085 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13085 0.011 Θ ∧ gammaRatio 13085 0.011 Θ ≤ 0.000083999082 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13085 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035273881498 : ℝ) * 0.525 / ((1 - 0.011) * 13085) := by gcongr
      _ ≤ (0.000083999082 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13085 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13085 0.011 Θ) :=
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
    badAllowance 13085 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13085 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13085 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13085 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13085 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13085 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13085 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13085 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13085 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13085 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13085 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035273881498 : ℝ) * 13085 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13085 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003175360227 + 0.003193459974 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13085

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13085
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13085 BstLean.Part154.csC) (piBar (rhoBar 13085 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13085 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13085 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13085 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13085 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13085 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13085 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13085 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13085 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13085 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13085 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13085 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13085 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13085 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13085 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051698115091 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13085) ≤ 0.010440081050 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13085 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035273881498)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010440081050 + 2 * 0.737676 / 13085) := by gcongr
    _ ≤ (0.051698115091 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13085 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13085

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13085
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520466855 : ℝ) ≤ plow 13085 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13085) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052358526714)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338380117) : eMP 13085 0.011 xi bn ≤ 0.001152723326 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13085 : ℝ) * (1 - 0.011))) ≤ 0.000570006344 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001338380117 / (13085 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000570006344 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000570006344 : ℝ) + 3.141593 * 0.052358526714 / (13085 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001152723326 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052358526714)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338380117) : PiBarMP 13085 12 0.011 xi bn ≤ 0.158837525649 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13085 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036583877829 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.758801857262 : ℝ) ≤ √((13085 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.389684849640 : ℝ) ≤ √(13085 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13085) ≤ 0.121797767702 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036583877829 + 0.052358526714 * 1.772454 / (2 * (113.758801857262 : ℝ))) * (1 + 0.001152723326) +
        8 / (13085 * 114.389684849640) + 0.121797767702 := by gcongr
    _ ≤ (0.158837525649 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052358526714)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338380117) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280517971559) :
    parallelOracle 13085 0.011 xi bn cd ≤ 0.159798625302 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13085 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13085 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520466855 : ℝ) ≤ plow 13085 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.389684849640 : ℝ) ≤ √(13085 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280517971559 : ℝ) / (2 * 0.560520466855 * 114.389684849640)) * 0.158837525649 +
        0.280517971559 ^ 2 / (2 * 0.560520466855 * 114.389684849640) := by gcongr
    _ ≤ (0.159798625302 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052358526714) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338380117)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280517971559) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13085 13085 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520466855 : ℝ) ≤ plow 13085 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.389684849640 : ℝ) ≤ √(13085 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13085 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13085 Θ 1.22 ≤ 0.011592832883 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.389684849640 := by gcongr <;> linarith
      _ ≤ (0.011592832883 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13085 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13085 13085 0.011 ≤ 0.008356408379 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13085 13085 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13085 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13085 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13085 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13085 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159798625302 + 0.011592832883 + (0.008356408379 : ℝ) *
        (1 + 2 * (0.280517971559 + 0.011592832883) / (0.560520466855 * 114.389684849640))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13085]

end BstLean.Part269.N13085

/-! The original eight local profiles supply actual 13085 moment certificates. -/
namespace BstLean.Part269.N13085
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13085 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13085 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13085 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052358526714 ∧
    0 ≤ bN 13085 BstLean.Part154.csC (groupTheta g) ∧ bN 13085 BstLean.Part154.csC (groupTheta g) ≤ 0.001338380117 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13085 13085 0.011
      (momentAllowance 13085 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13085 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13085 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13085 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13085 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13085 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228819856468 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13085 0.011
      (momentAllowance 13085 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13085 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13085
/-! The actual computed-centre upper energy formula at 13085. -/
namespace BstLean.Part269.N13085
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13085

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13085
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13085)
open BstLean.Part268 (cell13085)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084440375549
  | 2 => 0.085366210540
  | 3 => 0.086287831456
  | 4 => 0.087206102982
  | 5 => 0.088122086933
  | 6 => 0.089037073491
  | 7 => 0.089952615751
  | 8 => 0.090870567690
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13085 13085 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13085 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13085

/-! Actual upper energy certificates on all 43 source endpoints at 13085. -/
namespace BstLean.Part269.N13085
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13085)
open BstLean.Part268 (cell13085)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13085 (gMinus 13085) (1 - (cell13085 i).lower) ≤ 1 ∧
    energyUpper 13085 (gMinus 13085) (BstLean.Part211.gPlus 13085)
      (finiteEnergy 13085 13085 0.011) (1 - (cell13085 i).lower) ≤
      (cell13085 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨10,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨11,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨12,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨13,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨14,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨15,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨16,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨17,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨18,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨19,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨20,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨21,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨22,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨23,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨24,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨25,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨26,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨27,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨28,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨29,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨30,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨31,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨32,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨33,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨34,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨35,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨36,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨37,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨38,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨39,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨40,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨41,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨42,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨43,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨44,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨45,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨46,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨47,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨48,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨49,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨50,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨51,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13085) (by norm_num)
        (q := 1 - (cell13085 ⟨52,by decide⟩).lower)
        (by norm_num [cell13085]) (by norm_num [cell13085])
      exact ⟨E.1,E.2.trans (by norm_num [cell13085])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13085

/-! Source-cell containment and simple scalar guards at 13085. -/
namespace BstLean.Part269.N13085
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13085)
open BstLean.Part268 (cell13085)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13085 ⟨10,by decide⟩).lower ∧ (cell13085 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13085 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13085 ⟨11,by decide⟩).lower ∧ (cell13085 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13085 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13085 ⟨12,by decide⟩).lower ∧ (cell13085 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13085 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13085 ⟨13,by decide⟩).lower ∧ (cell13085 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13085 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13085 ⟨14,by decide⟩).lower ∧ (cell13085 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13085 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13085 ⟨15,by decide⟩).lower ∧ (cell13085 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13085 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13085 ⟨16,by decide⟩).lower ∧ (cell13085 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13085 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13085 ⟨17,by decide⟩).lower ∧ (cell13085 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13085 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13085 ⟨18,by decide⟩).lower ∧ (cell13085 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13085 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13085 ⟨19,by decide⟩).lower ∧ (cell13085 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13085 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13085 ⟨20,by decide⟩).lower ∧ (cell13085 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13085 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13085 ⟨21,by decide⟩).lower ∧ (cell13085 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13085 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13085 ⟨22,by decide⟩).lower ∧ (cell13085 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13085 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13085 ⟨23,by decide⟩).lower ∧ (cell13085 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13085 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13085 ⟨24,by decide⟩).lower ∧ (cell13085 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13085 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13085 ⟨25,by decide⟩).lower ∧ (cell13085 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13085 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13085 ⟨26,by decide⟩).lower ∧ (cell13085 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13085 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13085 ⟨27,by decide⟩).lower ∧ (cell13085 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13085 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13085 ⟨28,by decide⟩).lower ∧ (cell13085 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13085 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13085 ⟨29,by decide⟩).lower ∧ (cell13085 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13085 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13085 ⟨30,by decide⟩).lower ∧ (cell13085 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13085 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13085 ⟨31,by decide⟩).lower ∧ (cell13085 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13085 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13085 ⟨32,by decide⟩).lower ∧ (cell13085 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13085 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13085 ⟨33,by decide⟩).lower ∧ (cell13085 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13085 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13085 ⟨34,by decide⟩).lower ∧ (cell13085 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13085 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13085 ⟨35,by decide⟩).lower ∧ (cell13085 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13085 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13085 ⟨36,by decide⟩).lower ∧ (cell13085 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13085 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13085 ⟨37,by decide⟩).lower ∧ (cell13085 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13085 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13085 ⟨38,by decide⟩).lower ∧ (cell13085 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13085 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13085 ⟨39,by decide⟩).lower ∧ (cell13085 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13085 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13085 ⟨40,by decide⟩).lower ∧ (cell13085 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13085 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13085 ⟨41,by decide⟩).lower ∧ (cell13085 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13085 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13085 ⟨42,by decide⟩).lower ∧ (cell13085 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13085 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13085 ⟨43,by decide⟩).lower ∧ (cell13085 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13085 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13085 ⟨44,by decide⟩).lower ∧ (cell13085 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13085 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13085 ⟨45,by decide⟩).lower ∧ (cell13085 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13085 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13085 ⟨46,by decide⟩).lower ∧ (cell13085 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13085 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13085 ⟨47,by decide⟩).lower ∧ (cell13085 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13085 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13085 ⟨48,by decide⟩).lower ∧ (cell13085 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13085 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13085 ⟨49,by decide⟩).lower ∧ (cell13085 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13085 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13085 ⟨50,by decide⟩).lower ∧ (cell13085 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13085 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13085 ⟨51,by decide⟩).lower ∧ (cell13085 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13085 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13085 ⟨52,by decide⟩).lower ∧ (cell13085 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13085 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13085 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13085 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13085,cell13085,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13085 i).lower ∧
    (cell13085 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13085 i).upper ≤ (0.532 : ℝ) ∧
    (cell13085 i).centre ≤ (0.1 : ℝ) ∧ (cell13085 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13085 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13085 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13085

/-! The local source numeric instances at 13085 have no network premises. -/
namespace BstLean.Part269.N13085
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13085)
open BstLean.Part268 (cell13085)

noncomputable def sourceNumerics13085 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13085 (cell13085 i)
      scalarRow13085.M scalarRow13085.H scalarRow13085.xi := by
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
    energy_allowance := scalarRow13085.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13085]
    centre_nonneg := (scalarRow13085.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13085])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13085
/-! Actual 13086 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13086
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13086 ≤ (1.035272522021 : ℝ) := by
  have hr : (114.394055789625 : ℝ) ≤ √(13086 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.394055789625 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13086 13086 (11 / 1000) ≤
    (0.008356089083 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13086) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.394055789625 : ℝ) ≤ √(13086 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13086)
  have hdiv : K / √(13086 : ℝ) ≤ K / 114.394055789625 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.394055789625 ≤ (0.008356089083 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13086.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13086 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13086 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13086 := gPlus_lower 13086
end BstLean.Part269.N13086

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13086
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035272522020 : ℝ) ≤ wn 13086 := by
  have hn : √(13086 : ℝ) ≤ 114.394055789626 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13086 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.394055789626 ≤ 2 / √(13086 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244324434 : ℝ) ≤ rhoBar 13086 BstLean.Part154.csC ∧
    rhoBar 13086 BstLean.Part154.csC ≤ 0.000244324813 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035272522020 : ℝ) / (1.295212 * 13086) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035272522021 : ℝ) / (1.29521 * 13086) := by gcongr
      _ ≤ (0.000244324813 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13086 BstLean.Part154.csC) ≤ 0.000977358947 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13086 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13086 BstLean.Part154.csC) (piBar (rhoBar 13086 BstLean.Part154.csC)) ≤ 0.000186616680 ∧
    cc1 (rhoBar 13086 BstLean.Part154.csC) (piBar (rhoBar 13086 BstLean.Part154.csC)) ≤ 0.000118745486 ∧
    cc2 (rhoBar 13086 BstLean.Part154.csC) ≤ 0.000068932730 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13086 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13086 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13086 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13086 BstLean.Part154.csC * nuR (rhoBar 13086 BstLean.Part154.csC)) ≤ 0.000488664550 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244324813 : ℝ) * 0.000977358947 := by gcongr
      _ ≤ (0.000488664550 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13086 BstLean.Part154.csC) * nuR (rhoBar 13086 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000977358947 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13086 BstLean.Part154.csC) * rhoBar 13086 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244324813 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244324813 / 2 + 0.399 * 0.000977358947 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186616680 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488664550 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118745486 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244324813 / 1.414213562 := by gcongr
      _ ≤ (0.000068932730 : ℝ) := by norm_num

end BstLean.Part269.N13086

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13086
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13086 BstLean.Part154.csC) (piBar (rhoBar 13086 BstLean.Part154.csC)) ≤ 1.50396E-7 := by
  have hr0 : 0 ≤ rhoBar 13086 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13086 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13086 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13086 BstLean.Part154.csC) (piBar (rhoBar 13086 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13086 BstLean.Part154.csC) (piBar (rhoBar 13086 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13086 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186616680 : ℝ) ^ 2 + 0.000118745486 ^ 2 + 3 * 0.000068932730 ^ 2 +
        2 * 0.797885 * 0.000186616680 * 0.000118745486 + 2 * 0.000186616680 * 0.000068932730 +
        4 * 0.797885 * 0.000118745486 * 0.000068932730 := by gcongr
    _ ≤ (1.50396E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13086 BstLean.Part154.csC Θ ≤ 0.002549083507 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13086 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13086 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13086 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13086 BstLean.Part154.csC) (piBar (rhoBar 13086 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13086 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035272522021 * 1.50396E-7 / (0.000244324434 : ℝ) := by gcongr
    _ ≤ 0.002549083507 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13086 BstLean.Part154.csC Θ ≤ 0.002826880689 + 0.000644113597 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13086 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13086 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13086 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035272522021 : ℝ) * ((2 * Θ * 0.000244324813 +
        (6863 / 10000) * 0.000244324813 * 13086 * 0.000977358947) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002826880689 + 0.000644113597 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13086 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13086 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13086 0.011 Θ ∧ gammaRatio 13086 0.011 Θ ≤ 0.000083992553 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13086 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035272522021 : ℝ) * 0.525 / ((1 - 0.011) * 13086) := by gcongr
      _ ≤ (0.000083992553 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13086 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13086 0.011 Θ) :=
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
    badAllowance 13086 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13086 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13086 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13086 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13086 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13086 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13086 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13086 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13086 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13086 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13086 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035272522021 : ℝ) * 13086 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13086 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003175133037 + 0.003193197104 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13086

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13086
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13086 BstLean.Part154.csC) (piBar (rhoBar 13086 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13086 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13086 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13086 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13086 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13086 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13086 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13086 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13086 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13086 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13086 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13086 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13086 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13086 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13086 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051696118628 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13086) ≤ 0.010439682140 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13086 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035272522021)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010439682140 + 2 * 0.737676 / 13086) := by gcongr
    _ ≤ (0.051696118628 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13086 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13086

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13086
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520509452 : ℝ) ≤ plow 13086 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13086) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052358161517)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338268842) : eMP 13086 0.011 xi bn ≤ 0.001152631316 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13086 : ℝ) * (1 - 0.011))) ≤ 0.000569960869 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001338268842 / (13086 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569960869 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569960869 : ℝ) + 3.141593 * 0.052358161517 / (13086 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001152631316 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052358161517)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338268842) : PiBarMP 13086 12 0.011 xi bn ≤ 0.158831326745 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13086 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036582356978 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.763148690601 : ℝ) ≤ √((13086 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.394055789625 : ℝ) ≤ √(13086 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13086) ≤ 0.121793113870 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036582356978 + 0.052358161517 * 1.772454 / (2 * (113.763148690601 : ℝ))) * (1 + 0.001152631316) +
        8 / (13086 * 114.394055789625) + 0.121793113870 := by gcongr
    _ ≤ (0.158831326745 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052358161517)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338268842) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280515177094) :
    parallelOracle 13086 0.011 xi bn cd ≤ 0.159792360356 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13086 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13086 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520509452 : ℝ) ≤ plow 13086 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.394055789625 : ℝ) ≤ √(13086 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280515177094 : ℝ) / (2 * 0.560520509452 * 114.394055789625)) * 0.158831326745 +
        0.280515177094 ^ 2 / (2 * 0.560520509452 * 114.394055789625) := by gcongr
    _ ≤ (0.159792360356 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052358161517) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338268842)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280515177094) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13086 13086 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520509452 : ℝ) ≤ plow 13086 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.394055789625 : ℝ) ≤ √(13086 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13086 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13086 Θ 1.22 ≤ 0.011592389927 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.394055789625 := by gcongr <;> linarith
      _ ≤ (0.011592389927 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13086 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13086 13086 0.011 ≤ 0.008356089083 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13086 13086 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13086 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13086 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13086 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13086 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159792360356 + 0.011592389927 + (0.008356089083 : ℝ) *
        (1 + 2 * (0.280515177094 + 0.011592389927) / (0.560520509452 * 114.394055789625))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13086]

end BstLean.Part269.N13086

/-! The original eight local profiles supply actual 13086 moment certificates. -/
namespace BstLean.Part269.N13086
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13086 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13086 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13086 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052358161517 ∧
    0 ≤ bN 13086 BstLean.Part154.csC (groupTheta g) ∧ bN 13086 BstLean.Part154.csC (groupTheta g) ≤ 0.001338268842 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13086 13086 0.011
      (momentAllowance 13086 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13086 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13086 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13086 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13086 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13086 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228819058466 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13086 0.011
      (momentAllowance 13086 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13086 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13086
/-! The actual computed-centre upper energy formula at 13086. -/
namespace BstLean.Part269.N13086
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13086

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13086
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13086)
open BstLean.Part268 (cell13086)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084437823349
  | 2 => 0.085363626088
  | 3 => 0.086285210050
  | 4 => 0.087203438804
  | 5 => 0.088119372844
  | 6 => 0.089034300799
  | 7 => 0.089949773944
  | 8 => 0.090867644145
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13086 13086 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13086 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13086

/-! Actual upper energy certificates on all 43 source endpoints at 13086. -/
namespace BstLean.Part269.N13086
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13086)
open BstLean.Part268 (cell13086)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13086 (gMinus 13086) (1 - (cell13086 i).lower) ≤ 1 ∧
    energyUpper 13086 (gMinus 13086) (BstLean.Part211.gPlus 13086)
      (finiteEnergy 13086 13086 0.011) (1 - (cell13086 i).lower) ≤
      (cell13086 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨10,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨11,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨12,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨13,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨14,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨15,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨16,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨17,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨18,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨19,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨20,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨21,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨22,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨23,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨24,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨25,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨26,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨27,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨28,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨29,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨30,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨31,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨32,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨33,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨34,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨35,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨36,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨37,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨38,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨39,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨40,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨41,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨42,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨43,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨44,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨45,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨46,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨47,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨48,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨49,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨50,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨51,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13086) (by norm_num)
        (q := 1 - (cell13086 ⟨52,by decide⟩).lower)
        (by norm_num [cell13086]) (by norm_num [cell13086])
      exact ⟨E.1,E.2.trans (by norm_num [cell13086])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13086

/-! Source-cell containment and simple scalar guards at 13086. -/
namespace BstLean.Part269.N13086
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13086)
open BstLean.Part268 (cell13086)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13086 ⟨10,by decide⟩).lower ∧ (cell13086 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13086 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13086 ⟨11,by decide⟩).lower ∧ (cell13086 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13086 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13086 ⟨12,by decide⟩).lower ∧ (cell13086 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13086 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13086 ⟨13,by decide⟩).lower ∧ (cell13086 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13086 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13086 ⟨14,by decide⟩).lower ∧ (cell13086 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13086 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13086 ⟨15,by decide⟩).lower ∧ (cell13086 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13086 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13086 ⟨16,by decide⟩).lower ∧ (cell13086 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13086 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13086 ⟨17,by decide⟩).lower ∧ (cell13086 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13086 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13086 ⟨18,by decide⟩).lower ∧ (cell13086 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13086 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13086 ⟨19,by decide⟩).lower ∧ (cell13086 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13086 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13086 ⟨20,by decide⟩).lower ∧ (cell13086 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13086 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13086 ⟨21,by decide⟩).lower ∧ (cell13086 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13086 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13086 ⟨22,by decide⟩).lower ∧ (cell13086 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13086 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13086 ⟨23,by decide⟩).lower ∧ (cell13086 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13086 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13086 ⟨24,by decide⟩).lower ∧ (cell13086 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13086 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13086 ⟨25,by decide⟩).lower ∧ (cell13086 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13086 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13086 ⟨26,by decide⟩).lower ∧ (cell13086 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13086 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13086 ⟨27,by decide⟩).lower ∧ (cell13086 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13086 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13086 ⟨28,by decide⟩).lower ∧ (cell13086 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13086 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13086 ⟨29,by decide⟩).lower ∧ (cell13086 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13086 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13086 ⟨30,by decide⟩).lower ∧ (cell13086 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13086 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13086 ⟨31,by decide⟩).lower ∧ (cell13086 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13086 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13086 ⟨32,by decide⟩).lower ∧ (cell13086 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13086 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13086 ⟨33,by decide⟩).lower ∧ (cell13086 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13086 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13086 ⟨34,by decide⟩).lower ∧ (cell13086 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13086 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13086 ⟨35,by decide⟩).lower ∧ (cell13086 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13086 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13086 ⟨36,by decide⟩).lower ∧ (cell13086 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13086 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13086 ⟨37,by decide⟩).lower ∧ (cell13086 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13086 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13086 ⟨38,by decide⟩).lower ∧ (cell13086 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13086 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13086 ⟨39,by decide⟩).lower ∧ (cell13086 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13086 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13086 ⟨40,by decide⟩).lower ∧ (cell13086 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13086 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13086 ⟨41,by decide⟩).lower ∧ (cell13086 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13086 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13086 ⟨42,by decide⟩).lower ∧ (cell13086 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13086 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13086 ⟨43,by decide⟩).lower ∧ (cell13086 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13086 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13086 ⟨44,by decide⟩).lower ∧ (cell13086 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13086 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13086 ⟨45,by decide⟩).lower ∧ (cell13086 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13086 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13086 ⟨46,by decide⟩).lower ∧ (cell13086 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13086 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13086 ⟨47,by decide⟩).lower ∧ (cell13086 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13086 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13086 ⟨48,by decide⟩).lower ∧ (cell13086 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13086 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13086 ⟨49,by decide⟩).lower ∧ (cell13086 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13086 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13086 ⟨50,by decide⟩).lower ∧ (cell13086 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13086 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13086 ⟨51,by decide⟩).lower ∧ (cell13086 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13086 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13086 ⟨52,by decide⟩).lower ∧ (cell13086 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13086 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13086 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13086 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13086,cell13086,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13086 i).lower ∧
    (cell13086 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13086 i).upper ≤ (0.532 : ℝ) ∧
    (cell13086 i).centre ≤ (0.1 : ℝ) ∧ (cell13086 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13086 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13086 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13086

/-! The local source numeric instances at 13086 have no network premises. -/
namespace BstLean.Part269.N13086
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13086)
open BstLean.Part268 (cell13086)

noncomputable def sourceNumerics13086 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13086 (cell13086 i)
      scalarRow13086.M scalarRow13086.H scalarRow13086.xi := by
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
    energy_allowance := scalarRow13086.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13086]
    centre_nonneg := (scalarRow13086.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13086])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13086
/-! Actual 13087 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13087
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13087 ≤ (1.035271162700 : ℝ) := by
  have hr : (114.398426562606 : ℝ) ≤ √(13087 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.398426562606 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13087 13087 (11 / 1000) ≤
    (0.008355769823 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13087) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.398426562606 : ℝ) ≤ √(13087 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13087)
  have hdiv : K / √(13087 : ℝ) ≤ K / 114.398426562606 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.398426562606 ≤ (0.008355769823 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13087.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13087 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13087 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13087 := gPlus_lower 13087
end BstLean.Part269.N13087

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13087
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035271162699 : ℝ) ≤ wn 13087 := by
  have hn : √(13087 : ℝ) ≤ 114.398426562607 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13087 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.398426562607 ≤ 2 / √(13087 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000244305444 : ℝ) ≤ rhoBar 13087 BstLean.Part154.csC ∧
    rhoBar 13087 BstLean.Part154.csC ≤ 0.000244305823 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035271162699 : ℝ) / (1.295212 * 13087) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035271162700 : ℝ) / (1.29521 * 13087) := by gcongr
      _ ≤ (0.000244305823 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13087 BstLean.Part154.csC) ≤ 0.000977282978 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13087 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13087 BstLean.Part154.csC) (piBar (rhoBar 13087 BstLean.Part154.csC)) ≤ 0.000186602175 ∧
    cc1 (rhoBar 13087 BstLean.Part154.csC) (piBar (rhoBar 13087 BstLean.Part154.csC)) ≤ 0.000118736257 ∧
    cc2 (rhoBar 13087 BstLean.Part154.csC) ≤ 0.000068927372 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13087 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13087 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13087 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13087 BstLean.Part154.csC * nuR (rhoBar 13087 BstLean.Part154.csC)) ≤ 0.000488626568 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000244305823 : ℝ) * 0.000977282978 := by gcongr
      _ ≤ (0.000488626568 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13087 BstLean.Part154.csC) * nuR (rhoBar 13087 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000977282978 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13087 BstLean.Part154.csC) * rhoBar 13087 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000244305823 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000244305823 / 2 + 0.399 * 0.000977282978 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186602175 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000488626568 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118736257 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000244305823 / 1.414213562 := by gcongr
      _ ≤ (0.000068927372 : ℝ) := by norm_num

end BstLean.Part269.N13087

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13087
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13087 BstLean.Part154.csC) (piBar (rhoBar 13087 BstLean.Part154.csC)) ≤ 1.50373E-7 := by
  have hr0 : 0 ≤ rhoBar 13087 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13087 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13087 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13087 BstLean.Part154.csC) (piBar (rhoBar 13087 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13087 BstLean.Part154.csC) (piBar (rhoBar 13087 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13087 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186602175 : ℝ) ^ 2 + 0.000118736257 ^ 2 + 3 * 0.000068927372 ^ 2 +
        2 * 0.797885 * 0.000186602175 * 0.000118736257 + 2 * 0.000186602175 * 0.000068927372 +
        4 * 0.797885 * 0.000118736257 * 0.000068927372 := by gcongr
    _ ≤ (1.50373E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13087 BstLean.Part154.csC Θ ≤ 0.002548888441 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13087 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13087 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13087 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13087 BstLean.Part154.csC) (piBar (rhoBar 13087 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13087 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035271162700 * 1.50373E-7 / (0.000244305444 : ℝ) := by gcongr
    _ ≤ 0.002548888441 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13087 BstLean.Part154.csC Θ ≤ 0.002826653537 + 0.000644062688 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13087 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13087 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13087 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035271162700 : ℝ) * ((2 * Θ * 0.000244305823 +
        (6863 / 10000) * 0.000244305823 * 13087 * 0.000977282978) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002826653537 + 0.000644062688 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13087 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13087 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13087 0.011 Θ ∧ gammaRatio 13087 0.011 Θ ≤ 0.000083986025 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13087 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035271162700 : ℝ) * 0.525 / ((1 - 0.011) * 13087) := by gcongr
      _ ≤ (0.000083986025 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13087 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13087 0.011 Θ) :=
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
    badAllowance 13087 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000348252348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13087 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13087 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13087 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13087 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13087 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13087 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13087 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13087 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13087 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13087 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035271162700 : ℝ) * 13087 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000348252348 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13087 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003174905885 + 0.003192951129 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13087

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13087
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13087 BstLean.Part154.csC) (piBar (rhoBar 13087 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13087 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13087 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13087 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13087 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13087 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13087 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13087 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13087 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13087 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13087 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13087 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13087 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13087 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13087 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051694122392 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13087) ≤ 0.010439283275 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13087 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035271162700)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010439283275 + 2 * 0.737676 / 13087) := by gcongr
    _ ≤ (0.051694122392 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13087 12 ≤ 0.0015 := by
  exact BstLean.Part269.S29.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13087

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13087
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560520552044 : ℝ) ≤ plow 13087 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13087) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052357805228)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338166432) : eMP 13087 0.011 xi bn ≤ 0.001152543092 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13087 : ℝ) * (1 - 0.011))) ≤ 0.000569917286 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001338166432 / (13087 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000569917286 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000569917286 : ℝ) + 3.141593 * 0.052357805228 / (13087 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001152543092 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052357805228)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338166432) : PiBarMP 13087 12 0.011 xi bn ≤ 0.158825249831 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13087 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036580957232 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.767495357856 : ℝ) ≤ √((13087 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.398426562606 : ℝ) ≤ √(13087 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13087) ≤ 0.121788460571 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036580957232 + 0.052357805228 * 1.772454 / (2 * (113.767495357856 : ℝ))) * (1 + 0.001152543092) +
        8 / (13087 * 114.398426562606) + 0.121788460571 := by gcongr
    _ ≤ (0.158825249831 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052357805228)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338166432) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280512402318) :
    parallelOracle 13087 0.011 xi bn cd ≤ 0.159786217784 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13087 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13087 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560520552044 : ℝ) ≤ plow 13087 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.398426562606 : ℝ) ≤ √(13087 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280512402318 : ℝ) / (2 * 0.560520552044 * 114.398426562606)) * 0.158825249831 +
        0.280512402318 ^ 2 / (2 * 0.560520552044 * 114.398426562606) := by gcongr
    _ ≤ (0.159786217784 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052357805228) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001338166432)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280512402318) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13087 13087 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560520552044 : ℝ) ≤ plow 13087 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.398426562606 : ℝ) ≤ √(13087 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13087 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13087 Θ 1.22 ≤ 0.011591947022 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.398426562606 := by gcongr <;> linarith
      _ ≤ (0.011591947022 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13087 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13087 13087 0.011 ≤ 0.008355769823 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13087 13087 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13087 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13087 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13087 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13087 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159786217784 + 0.011591947022 + (0.008355769823 : ℝ) *
        (1 + 2 * (0.280512402318 + 0.011591947022) / (0.560520552044 * 114.398426562606))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13087]

end BstLean.Part269.N13087

/-! The original eight local profiles supply actual 13087 moment certificates. -/
namespace BstLean.Part269.N13087
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13087 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13087 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13087 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052357805228 ∧
    0 ≤ bN 13087 BstLean.Part154.csC (groupTheta g) ∧ bN 13087 BstLean.Part154.csC (groupTheta g) ≤ 0.001338166432 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13087 13087 0.011
      (momentAllowance 13087 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13087 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13087 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13087 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13087 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13087 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228818279926 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13087 0.011
      (momentAllowance 13087 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13087 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13087
/-! The actual computed-centre upper energy formula at 13087. -/
namespace BstLean.Part269.N13087
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13087

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13087
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13087)
open BstLean.Part268 (cell13087)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084435271896
  | 2 => 0.085361042409
  | 3 => 0.086282589449
  | 4 => 0.087200775470
  | 5 => 0.088116659648
  | 6 => 0.089031529057
  | 7 => 0.089946933158
  | 8 => 0.090864721708
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13087 13087 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13087 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
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

end BstLean.Part269.N13087

/-! Actual upper energy certificates on all 43 source endpoints at 13087. -/
namespace BstLean.Part269.N13087
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13087)
open BstLean.Part268 (cell13087)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13087 (gMinus 13087) (1 - (cell13087 i).lower) ≤ 1 ∧
    energyUpper 13087 (gMinus 13087) (BstLean.Part211.gPlus 13087)
      (finiteEnergy 13087 13087 0.011) (1 - (cell13087 i).lower) ≤
      (cell13087 i).energy := by
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
      have E := BstLean.Part269.S29.uniformEnergy10 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨10,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy11 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨11,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy12 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨12,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy13 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨13,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy14 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨14,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy15 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨15,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy16 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨16,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy17 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨17,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy18 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨18,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy19 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨19,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy20 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨20,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy21 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨21,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy22 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨22,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy23 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨23,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy24 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨24,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy25 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨25,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy26 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨26,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy27 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨27,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy28 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨28,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy29 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨29,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy30 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨30,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy31 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨31,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy32 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨32,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy33 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨33,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy34 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨34,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy35 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨35,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy36 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨36,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy37 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨37,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy38 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨38,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy39 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨39,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy40 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨40,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy41 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨41,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy42 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨42,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy43 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨43,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy44 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨44,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy45 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨45,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy46 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨46,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy47 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨47,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy48 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨48,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy49 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨49,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy50 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨50,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy51 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨51,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S29.uniformEnergy52 (n := 13087) (by norm_num)
        (q := 1 - (cell13087 ⟨52,by decide⟩).lower)
        (by norm_num [cell13087]) (by norm_num [cell13087])
      exact ⟨E.1,E.2.trans (by norm_num [cell13087])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13087

/-! Source-cell containment and simple scalar guards at 13087. -/
namespace BstLean.Part269.N13087
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13087)
open BstLean.Part268 (cell13087)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13087 ⟨10,by decide⟩).lower ∧ (cell13087 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13087 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13087 ⟨11,by decide⟩).lower ∧ (cell13087 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13087 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13087 ⟨12,by decide⟩).lower ∧ (cell13087 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13087 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13087 ⟨13,by decide⟩).lower ∧ (cell13087 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13087 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13087 ⟨14,by decide⟩).lower ∧ (cell13087 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13087 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13087 ⟨15,by decide⟩).lower ∧ (cell13087 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13087 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13087 ⟨16,by decide⟩).lower ∧ (cell13087 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13087 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13087 ⟨17,by decide⟩).lower ∧ (cell13087 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13087 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13087 ⟨18,by decide⟩).lower ∧ (cell13087 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13087 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13087 ⟨19,by decide⟩).lower ∧ (cell13087 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13087 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13087 ⟨20,by decide⟩).lower ∧ (cell13087 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13087 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13087 ⟨21,by decide⟩).lower ∧ (cell13087 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13087 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13087 ⟨22,by decide⟩).lower ∧ (cell13087 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13087 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13087 ⟨23,by decide⟩).lower ∧ (cell13087 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13087 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13087 ⟨24,by decide⟩).lower ∧ (cell13087 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13087 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13087 ⟨25,by decide⟩).lower ∧ (cell13087 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13087 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13087 ⟨26,by decide⟩).lower ∧ (cell13087 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13087 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13087 ⟨27,by decide⟩).lower ∧ (cell13087 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13087 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13087 ⟨28,by decide⟩).lower ∧ (cell13087 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13087 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13087 ⟨29,by decide⟩).lower ∧ (cell13087 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13087 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13087 ⟨30,by decide⟩).lower ∧ (cell13087 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13087 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13087 ⟨31,by decide⟩).lower ∧ (cell13087 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13087 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13087 ⟨32,by decide⟩).lower ∧ (cell13087 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13087 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13087 ⟨33,by decide⟩).lower ∧ (cell13087 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13087 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13087 ⟨34,by decide⟩).lower ∧ (cell13087 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13087 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13087 ⟨35,by decide⟩).lower ∧ (cell13087 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13087 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13087 ⟨36,by decide⟩).lower ∧ (cell13087 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13087 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13087 ⟨37,by decide⟩).lower ∧ (cell13087 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13087 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13087 ⟨38,by decide⟩).lower ∧ (cell13087 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13087 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13087 ⟨39,by decide⟩).lower ∧ (cell13087 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13087 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13087 ⟨40,by decide⟩).lower ∧ (cell13087 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13087 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13087 ⟨41,by decide⟩).lower ∧ (cell13087 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13087 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13087 ⟨42,by decide⟩).lower ∧ (cell13087 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13087 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13087 ⟨43,by decide⟩).lower ∧ (cell13087 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13087 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13087 ⟨44,by decide⟩).lower ∧ (cell13087 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13087 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13087 ⟨45,by decide⟩).lower ∧ (cell13087 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13087 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13087 ⟨46,by decide⟩).lower ∧ (cell13087 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13087 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13087 ⟨47,by decide⟩).lower ∧ (cell13087 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13087 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13087 ⟨48,by decide⟩).lower ∧ (cell13087 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13087 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13087 ⟨49,by decide⟩).lower ∧ (cell13087 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13087 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13087 ⟨50,by decide⟩).lower ∧ (cell13087 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13087 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13087 ⟨51,by decide⟩).lower ∧ (cell13087 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13087 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13087 ⟨52,by decide⟩).lower ∧ (cell13087 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13087 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13087 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13087 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13087,cell13087,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13087 i).lower ∧
    (cell13087 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13087 i).upper ≤ (0.532 : ℝ) ∧
    (cell13087 i).centre ≤ (0.1 : ℝ) ∧ (cell13087 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13087 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13087 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13087

/-! The local source numeric instances at 13087 have no network premises. -/
namespace BstLean.Part269.N13087
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13087)
open BstLean.Part268 (cell13087)

noncomputable def sourceNumerics13087 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13087 (cell13087 i)
      scalarRow13087.M scalarRow13087.H scalarRow13087.xi := by
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
    energy_allowance := scalarRow13087.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13087]
    centre_nonneg := (scalarRow13087.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D29.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13087])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13087