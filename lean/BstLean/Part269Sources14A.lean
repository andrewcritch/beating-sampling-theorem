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
import BstLean.Part269Direction14
import BstLean.Part269Shared14
import BstLean.Part269Finite
import BstLean.Part269Rows14
import BstLean.Part269Source
/-! Actual 12700 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12700
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12700 ≤ (1.035809221007 : ℝ) := by
  have hr : (112.694276695846 : ℝ) ≤ √(12700 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.694276695846 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12700 12700 (11 / 1000) ≤
    (0.008482125776 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12700) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.694276695846 : ℝ) ≤ √(12700 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12700)
  have hdiv : K / √(12700 : ℝ) ≤ K / 112.694276695846 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.694276695846 ≤ (0.008482125776 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12700.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12700 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12700 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12700 := gPlus_lower 12700
end BstLean.Part269.N12700

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12700
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035809221006 : ℝ) ≤ wn 12700 := by
  have hn : √(12700 : ℝ) ≤ 112.694276695847 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12700 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.694276695847 ≤ 2 / √(12700 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251880869 : ℝ) ≤ rhoBar 12700 BstLean.Part154.csC ∧
    rhoBar 12700 BstLean.Part154.csC ≤ 0.000251881259 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035809221006 : ℝ) / (1.295212 * 12700) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035809221007 : ℝ) / (1.29521 * 12700) := by gcongr
      _ ≤ (0.000251881259 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12700 BstLean.Part154.csC) ≤ 0.001007588481 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12700 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12700 BstLean.Part154.csC) (piBar (rhoBar 12700 BstLean.Part154.csC)) ≤ 0.000192388605 ∧
    cc1 (rhoBar 12700 BstLean.Part154.csC) (piBar (rhoBar 12700 BstLean.Part154.csC)) ≤ 0.000122418147 ∧
    cc2 (rhoBar 12700 BstLean.Part154.csC) ≤ 0.000071064672 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12700 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12700 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12700 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12700 BstLean.Part154.csC * nuR (rhoBar 12700 BstLean.Part154.csC)) ≤ 0.000503778380 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251881259 : ℝ) * 0.001007588481 := by gcongr
      _ ≤ (0.000503778380 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12700 BstLean.Part154.csC) * nuR (rhoBar 12700 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001007588481 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12700 BstLean.Part154.csC) * rhoBar 12700 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251881259 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251881259 / 2 + 0.399 * 0.001007588481 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192388605 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503778380 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122418147 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251881259 / 1.414213562 := by gcongr
      _ ≤ (0.000071064672 : ℝ) := by norm_num

end BstLean.Part269.N12700

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12700
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12700 BstLean.Part154.csC) (piBar (rhoBar 12700 BstLean.Part154.csC)) ≤ 1.59843E-7 := by
  have hr0 : 0 ≤ rhoBar 12700 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12700 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12700 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12700 BstLean.Part154.csC) (piBar (rhoBar 12700 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12700 BstLean.Part154.csC) (piBar (rhoBar 12700 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12700 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192388605 : ℝ) ^ 2 + 0.000122418147 ^ 2 + 3 * 0.000071064672 ^ 2 +
        2 * 0.797885 * 0.000192388605 * 0.000122418147 + 2 * 0.000192388605 * 0.000071064672 +
        4 * 0.797885 * 0.000122418147 * 0.000071064672 := by gcongr
    _ ≤ (1.59843E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12700 BstLean.Part154.csC Θ ≤ 0.002629288266 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12700 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12700 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12700 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12700 BstLean.Part154.csC) (piBar (rhoBar 12700 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12700 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035809221007 * 1.59843E-7 / (0.000251880869 : ℝ) := by gcongr
    _ ≤ 0.002629288266 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12700 BstLean.Part154.csC Θ ≤ 0.002917338014 + 0.000664378903 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12700 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12700 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12700 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035809221007 : ℝ) * ((2 * Θ * 0.000251881259 +
        (6863 / 10000) * 0.000251881259 * 12700 * 0.001007588481) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002917338014 + 0.000664378903 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12700 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12700 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12700 0.011 Θ ∧ gammaRatio 12700 0.011 Θ ≤ 0.000086590264 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12700 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035809221007 : ℝ) * 0.525 / ((1 - 0.011) * 12700) := by gcongr
      _ ≤ (0.000086590264 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12700 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12700 0.011 Θ) :=
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
    badAllowance 12700 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12700 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12700 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12700 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12700 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12700 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12700 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12700 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12700 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12700 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12700 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035809221007 : ℝ) * 12700 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12700 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003533030491 + 0.003293667169 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12700

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12700
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12700 BstLean.Part154.csC) (piBar (rhoBar 12700 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12700 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12700 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12700 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12700 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12700 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12700 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12700 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12700 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12700 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12700 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12700 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12700 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12700 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12700 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052484312798 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12700) ≤ 0.010597144914 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12700 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035809221007)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010597144914 + 2 * 0.737676 / 12700) := by gcongr
    _ ≤ (0.052484312798 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12700 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12700

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12700
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503568291 : ℝ) ≤ plow 12700 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12700) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052768805755)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380376340) : eMP 12700 0.011 xi bn ≤ 0.001188376717 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12700 : ℝ) * (1 - 0.011))) ≤ 0.000587589069 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001380376340 / (12700 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587589069 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587589069 : ℝ) + 3.141593 * 0.052768805755 / (12700 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001188376717 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052768805755)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380376340) : PiBarMP 12700 12 0.011 xi bn ≤ 0.161251060559 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12700 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037153416263 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.072744233377 : ℝ) ≤ √((12700 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.694276695846 : ℝ) ≤ √(12700 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12700) ≤ 0.123630131638 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037153416263 + 0.052768805755 * 1.772454 / (2 * (112.072744233377 : ℝ))) * (1 + 0.001188376717) +
        8 / (12700 * 112.694276695846) + 0.123630131638 := by gcongr
    _ ≤ (0.161251060559 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052768805755)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380376340) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282198930868) :
    parallelOracle 12700 0.011 xi bn cd ≤ 0.162241641065 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12700 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12700 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503568291 : ℝ) ≤ plow 12700 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.694276695846 : ℝ) ≤ √(12700 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282198930868 : ℝ) / (2 * 0.560503568291 * 112.694276695846)) * 0.161251060559 +
        0.282198930868 ^ 2 / (2 * 0.560503568291 * 112.694276695846) := by gcongr
    _ ≤ (0.162241641065 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052768805755) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380376340)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282198930868) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12700 12700 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503568291 : ℝ) ≤ plow 12700 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.694276695846 : ℝ) ≤ √(12700 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12700 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12700 Θ 1.22 ≤ 0.011767239109 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.694276695846 := by gcongr <;> linarith
      _ ≤ (0.011767239109 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12700 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12700 12700 0.011 ≤ 0.008482125776 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12700 12700 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12700 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12700 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12700 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12700 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162241641065 + 0.011767239109 + (0.008482125776 : ℝ) *
        (1 + 2 * (0.282198930868 + 0.011767239109) / (0.560503568291 * 112.694276695846))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12700]

end BstLean.Part269.N12700

/-! The original eight local profiles supply actual 12700 moment certificates. -/
namespace BstLean.Part269.N12700
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12700 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12700 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12700 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052768805755 ∧
    0 ≤ bN 12700 BstLean.Part154.csC (groupTheta g) ∧ bN 12700 BstLean.Part154.csC (groupTheta g) ≤ 0.001380376340 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12700 12700 0.011
      (momentAllowance 12700 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12700 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12700 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12700 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12700 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12700 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229714618070 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12700 0.011
      (momentAllowance 12700 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12700 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12700
/-! The actual computed-centre upper energy formula at 12700. -/
namespace BstLean.Part269.N12700
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12700

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12700
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12700)
open BstLean.Part268 (cell12700)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085490256211
  | 2 => 0.086433005476
  | 3 => 0.087373894369
  | 4 => 0.088314340953
  | 5 => 0.089256060449
  | 6 => 0.090201109380
  | 7 => 0.091151933858
  | 8 => 0.092111422074
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12700 12700 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12700 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003533030491 + 0.003293667169 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S14.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12700

/-! Actual upper energy certificates on all 43 source endpoints at 12700. -/
namespace BstLean.Part269.N12700
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12700)
open BstLean.Part268 (cell12700)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12700 (gMinus 12700) (1 - (cell12700 i).lower) ≤ 1 ∧
    energyUpper 12700 (gMinus 12700) (BstLean.Part211.gPlus 12700)
      (finiteEnergy 12700 12700 0.011) (1 - (cell12700 i).lower) ≤
      (cell12700 i).energy := by
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨10,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨11,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨12,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨13,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨14,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨15,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨16,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨17,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨18,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨19,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨20,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨21,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨22,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨23,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨24,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨25,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨26,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨27,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨28,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨29,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨30,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨31,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨32,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨33,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨34,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨35,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨36,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨37,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨38,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨39,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨40,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨41,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨42,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨43,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨44,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨45,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨46,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨47,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨48,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨49,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨50,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨51,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12700) (by norm_num)
        (q := 1 - (cell12700 ⟨52,by decide⟩).lower)
        (by norm_num [cell12700]) (by norm_num [cell12700])
      exact ⟨E.1,E.2.trans (by norm_num [cell12700])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12700

/-! Source-cell containment and simple scalar guards at 12700. -/
namespace BstLean.Part269.N12700
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12700)
open BstLean.Part268 (cell12700)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12700 ⟨10,by decide⟩).lower ∧ (cell12700 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12700 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12700 ⟨11,by decide⟩).lower ∧ (cell12700 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12700 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12700 ⟨12,by decide⟩).lower ∧ (cell12700 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12700 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12700 ⟨13,by decide⟩).lower ∧ (cell12700 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12700 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12700 ⟨14,by decide⟩).lower ∧ (cell12700 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12700 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12700 ⟨15,by decide⟩).lower ∧ (cell12700 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12700 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12700 ⟨16,by decide⟩).lower ∧ (cell12700 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12700 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12700 ⟨17,by decide⟩).lower ∧ (cell12700 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12700 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12700 ⟨18,by decide⟩).lower ∧ (cell12700 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12700 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12700 ⟨19,by decide⟩).lower ∧ (cell12700 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12700 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12700 ⟨20,by decide⟩).lower ∧ (cell12700 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12700 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12700 ⟨21,by decide⟩).lower ∧ (cell12700 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12700 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12700 ⟨22,by decide⟩).lower ∧ (cell12700 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12700 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12700 ⟨23,by decide⟩).lower ∧ (cell12700 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12700 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12700 ⟨24,by decide⟩).lower ∧ (cell12700 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12700 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12700 ⟨25,by decide⟩).lower ∧ (cell12700 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12700 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12700 ⟨26,by decide⟩).lower ∧ (cell12700 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12700 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12700 ⟨27,by decide⟩).lower ∧ (cell12700 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12700 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12700 ⟨28,by decide⟩).lower ∧ (cell12700 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12700 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12700 ⟨29,by decide⟩).lower ∧ (cell12700 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12700 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12700 ⟨30,by decide⟩).lower ∧ (cell12700 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12700 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12700 ⟨31,by decide⟩).lower ∧ (cell12700 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12700 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12700 ⟨32,by decide⟩).lower ∧ (cell12700 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12700 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12700 ⟨33,by decide⟩).lower ∧ (cell12700 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12700 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12700 ⟨34,by decide⟩).lower ∧ (cell12700 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12700 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12700 ⟨35,by decide⟩).lower ∧ (cell12700 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12700 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12700 ⟨36,by decide⟩).lower ∧ (cell12700 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12700 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12700 ⟨37,by decide⟩).lower ∧ (cell12700 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12700 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12700 ⟨38,by decide⟩).lower ∧ (cell12700 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12700 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12700 ⟨39,by decide⟩).lower ∧ (cell12700 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12700 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12700 ⟨40,by decide⟩).lower ∧ (cell12700 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12700 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12700 ⟨41,by decide⟩).lower ∧ (cell12700 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12700 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12700 ⟨42,by decide⟩).lower ∧ (cell12700 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12700 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12700 ⟨43,by decide⟩).lower ∧ (cell12700 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12700 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12700 ⟨44,by decide⟩).lower ∧ (cell12700 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12700 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12700 ⟨45,by decide⟩).lower ∧ (cell12700 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12700 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12700 ⟨46,by decide⟩).lower ∧ (cell12700 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12700 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12700 ⟨47,by decide⟩).lower ∧ (cell12700 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12700 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12700 ⟨48,by decide⟩).lower ∧ (cell12700 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12700 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12700 ⟨49,by decide⟩).lower ∧ (cell12700 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12700 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12700 ⟨50,by decide⟩).lower ∧ (cell12700 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12700 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12700 ⟨51,by decide⟩).lower ∧ (cell12700 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12700 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12700 ⟨52,by decide⟩).lower ∧ (cell12700 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12700 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12700 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12700 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12700,cell12700,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12700 i).lower ∧
    (cell12700 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12700 i).upper ≤ (0.532 : ℝ) ∧
    (cell12700 i).centre ≤ (0.1 : ℝ) ∧ (cell12700 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12700 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12700 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12700

/-! The local source numeric instances at 12700 have no network premises. -/
namespace BstLean.Part269.N12700
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12700)
open BstLean.Part268 (cell12700)

noncomputable def sourceNumerics12700 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12700 (cell12700 i)
      scalarRow12700.M scalarRow12700.H scalarRow12700.xi := by
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
    energy_allowance := scalarRow12700.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12700]
    centre_nonneg := (scalarRow12700.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12700])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12700
/-! Actual 12701 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12701
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12701 ≤ (1.035807798880 : ℝ) := by
  have hr : (112.698713391058 : ℝ) ≤ √(12701 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.698713391058 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12701 12701 (11 / 1000) ≤
    (0.008481791851 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12701) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.698713391058 : ℝ) ≤ √(12701 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12701)
  have hdiv : K / √(12701 : ℝ) ≤ K / 112.698713391058 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.698713391058 ≤ (0.008481791851 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12701.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12701 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12701 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12701 := gPlus_lower 12701
end BstLean.Part269.N12701

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12701
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035807798879 : ℝ) ≤ wn 12701 := by
  have hn : √(12701 : ℝ) ≤ 112.698713391059 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12701 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.698713391059 ≤ 2 / √(12701 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251860692 : ℝ) ≤ rhoBar 12701 BstLean.Part154.csC ∧
    rhoBar 12701 BstLean.Part154.csC ≤ 0.000251861082 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035807798879 : ℝ) / (1.295212 * 12701) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035807798880 : ℝ) / (1.29521 * 12701) := by gcongr
      _ ≤ (0.000251861082 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12701 BstLean.Part154.csC) ≤ 0.001007507763 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12701 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12701 BstLean.Part154.csC) (piBar (rhoBar 12701 BstLean.Part154.csC)) ≤ 0.000192373193 ∧
    cc1 (rhoBar 12701 BstLean.Part154.csC) (piBar (rhoBar 12701 BstLean.Part154.csC)) ≤ 0.000122408340 ∧
    cc2 (rhoBar 12701 BstLean.Part154.csC) ≤ 0.000071058979 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12701 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12701 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12701 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12701 BstLean.Part154.csC * nuR (rhoBar 12701 BstLean.Part154.csC)) ≤ 0.000503738023 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251861082 : ℝ) * 0.001007507763 := by gcongr
      _ ≤ (0.000503738023 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12701 BstLean.Part154.csC) * nuR (rhoBar 12701 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001007507763 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12701 BstLean.Part154.csC) * rhoBar 12701 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251861082 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251861082 / 2 + 0.399 * 0.001007507763 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192373193 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503738023 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122408340 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251861082 / 1.414213562 := by gcongr
      _ ≤ (0.000071058979 : ℝ) := by norm_num

end BstLean.Part269.N12701

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12701
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12701 BstLean.Part154.csC) (piBar (rhoBar 12701 BstLean.Part154.csC)) ≤ 1.59818E-7 := by
  have hr0 : 0 ≤ rhoBar 12701 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12701 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12701 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12701 BstLean.Part154.csC) (piBar (rhoBar 12701 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12701 BstLean.Part154.csC) (piBar (rhoBar 12701 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12701 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192373193 : ℝ) ^ 2 + 0.000122408340 ^ 2 + 3 * 0.000071058979 ^ 2 +
        2 * 0.797885 * 0.000192373193 * 0.000122408340 + 2 * 0.000192373193 * 0.000071058979 +
        4 * 0.797885 * 0.000122408340 * 0.000071058979 := by gcongr
    _ ≤ (1.59818E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12701 BstLean.Part154.csC Θ ≤ 0.002629084031 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12701 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12701 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12701 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12701 BstLean.Part154.csC) (piBar (rhoBar 12701 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12701 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035807798880 * 1.59818E-7 / (0.000251860692 : ℝ) := by gcongr
    _ ≤ 0.002629084031 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12701 BstLean.Part154.csC Θ ≤ 0.002917096301 + 0.000664324771 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12701 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12701 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12701 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035807798880 : ℝ) * ((2 * Θ * 0.000251861082 +
        (6863 / 10000) * 0.000251861082 * 12701 * 0.001007507763) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002917096301 + 0.000664324771 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12701 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12701 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12701 0.011 Θ ∧ gammaRatio 12701 0.011 Θ ≤ 0.000086583327 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12701 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035807798880 : ℝ) * 0.525 / ((1 - 0.011) * 12701) := by gcongr
      _ ≤ (0.000086583327 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12701 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12701 0.011 Θ) :=
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
    badAllowance 12701 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12701 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12701 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12701 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12701 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12701 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12701 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12701 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12701 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12701 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12701 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035807798880 : ℝ) * 12701 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12701 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003532788778 + 0.003293408802 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12701

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12701
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12701 BstLean.Part154.csC) (piBar (rhoBar 12701 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12701 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12701 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12701 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12701 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12701 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12701 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12701 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12701 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12701 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12701 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12701 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12701 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12701 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12701 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052482224203 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12701) ≤ 0.010596727728 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12701 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035807798880)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010596727728 + 2 * 0.737676 / 12701) := by gcongr
    _ ≤ (0.052482224203 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12701 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12701

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12701
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503613510 : ℝ) ≤ plow 12701 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12701) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052768428400)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380269117) : eMP 12701 0.011 xi bn ≤ 0.001188283678 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12701 : ℝ) * (1 - 0.011))) ≤ 0.000587543116 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001380269117 / (12701 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587543116 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587543116 : ℝ) + 3.141593 * 0.052768428400 / (12701 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001188283678 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052768428400)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380269117) : PiBarMP 12701 12 0.011 xi bn ≤ 0.161244725211 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12701 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037151973259 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.077156459289 : ℝ) ≤ √((12701 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.698713391058 : ℝ) ≤ √(12701 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12701) ≤ 0.123625264598 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037151973259 + 0.052768428400 * 1.772454 / (2 * (112.077156459289 : ℝ))) * (1 + 0.001188283678) +
        8 / (12701 * 112.698713391058) + 0.123625264598 := by gcongr
    _ ≤ (0.161244725211 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052768428400)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380269117) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282196020916) :
    parallelOracle 12701 0.011 xi bn cd ≤ 0.162235235775 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12701 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12701 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503613510 : ℝ) ≤ plow 12701 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.698713391058 : ℝ) ≤ √(12701 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282196020916 : ℝ) / (2 * 0.560503613510 * 112.698713391058)) * 0.161244725211 +
        0.282196020916 ^ 2 / (2 * 0.560503613510 * 112.698713391058) := by gcongr
    _ ≤ (0.162235235775 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052768428400) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380269117)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282196020916) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12701 12701 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503613510 : ℝ) ≤ plow 12701 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.698713391058 : ℝ) ≤ √(12701 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12701 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12701 Θ 1.22 ≤ 0.011766775859 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.698713391058 := by gcongr <;> linarith
      _ ≤ (0.011766775859 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12701 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12701 12701 0.011 ≤ 0.008481791851 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12701 12701 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12701 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12701 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12701 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12701 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162235235775 + 0.011766775859 + (0.008481791851 : ℝ) *
        (1 + 2 * (0.282196020916 + 0.011766775859) / (0.560503613510 * 112.698713391058))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12701]

end BstLean.Part269.N12701

/-! The original eight local profiles supply actual 12701 moment certificates. -/
namespace BstLean.Part269.N12701
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12701 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12701 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12701 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052768428400 ∧
    0 ≤ bN 12701 BstLean.Part154.csC (groupTheta g) ∧ bN 12701 BstLean.Part154.csC (groupTheta g) ≤ 0.001380269117 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12701 12701 0.011
      (momentAllowance 12701 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12701 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12701 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12701 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12701 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12701 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229713796713 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12701 0.011
      (momentAllowance 12701 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12701 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12701
/-! The actual computed-centre upper energy formula at 12701. -/
namespace BstLean.Part269.N12701
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12701

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12701
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12701)
open BstLean.Part268 (cell12701)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085487340458
  | 2 => 0.086430036167
  | 3 => 0.087370863693
  | 4 => 0.088311239299
  | 5 => 0.089252876089
  | 6 => 0.090197828112
  | 7 => 0.091148538608
  | 8 => 0.092107892448
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12701 12701 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12701 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003533030491 + 0.003293667169 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S14.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12701

/-! Actual upper energy certificates on all 43 source endpoints at 12701. -/
namespace BstLean.Part269.N12701
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12701)
open BstLean.Part268 (cell12701)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12701 (gMinus 12701) (1 - (cell12701 i).lower) ≤ 1 ∧
    energyUpper 12701 (gMinus 12701) (BstLean.Part211.gPlus 12701)
      (finiteEnergy 12701 12701 0.011) (1 - (cell12701 i).lower) ≤
      (cell12701 i).energy := by
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨10,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨11,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨12,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨13,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨14,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨15,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨16,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨17,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨18,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨19,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨20,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨21,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨22,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨23,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨24,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨25,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨26,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨27,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨28,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨29,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨30,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨31,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨32,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨33,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨34,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨35,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨36,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨37,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨38,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨39,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨40,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨41,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨42,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨43,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨44,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨45,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨46,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨47,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨48,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨49,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨50,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨51,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12701) (by norm_num)
        (q := 1 - (cell12701 ⟨52,by decide⟩).lower)
        (by norm_num [cell12701]) (by norm_num [cell12701])
      exact ⟨E.1,E.2.trans (by norm_num [cell12701])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12701

/-! Source-cell containment and simple scalar guards at 12701. -/
namespace BstLean.Part269.N12701
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12701)
open BstLean.Part268 (cell12701)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12701 ⟨10,by decide⟩).lower ∧ (cell12701 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12701 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12701 ⟨11,by decide⟩).lower ∧ (cell12701 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12701 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12701 ⟨12,by decide⟩).lower ∧ (cell12701 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12701 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12701 ⟨13,by decide⟩).lower ∧ (cell12701 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12701 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12701 ⟨14,by decide⟩).lower ∧ (cell12701 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12701 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12701 ⟨15,by decide⟩).lower ∧ (cell12701 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12701 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12701 ⟨16,by decide⟩).lower ∧ (cell12701 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12701 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12701 ⟨17,by decide⟩).lower ∧ (cell12701 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12701 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12701 ⟨18,by decide⟩).lower ∧ (cell12701 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12701 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12701 ⟨19,by decide⟩).lower ∧ (cell12701 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12701 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12701 ⟨20,by decide⟩).lower ∧ (cell12701 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12701 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12701 ⟨21,by decide⟩).lower ∧ (cell12701 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12701 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12701 ⟨22,by decide⟩).lower ∧ (cell12701 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12701 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12701 ⟨23,by decide⟩).lower ∧ (cell12701 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12701 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12701 ⟨24,by decide⟩).lower ∧ (cell12701 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12701 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12701 ⟨25,by decide⟩).lower ∧ (cell12701 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12701 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12701 ⟨26,by decide⟩).lower ∧ (cell12701 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12701 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12701 ⟨27,by decide⟩).lower ∧ (cell12701 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12701 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12701 ⟨28,by decide⟩).lower ∧ (cell12701 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12701 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12701 ⟨29,by decide⟩).lower ∧ (cell12701 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12701 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12701 ⟨30,by decide⟩).lower ∧ (cell12701 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12701 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12701 ⟨31,by decide⟩).lower ∧ (cell12701 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12701 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12701 ⟨32,by decide⟩).lower ∧ (cell12701 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12701 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12701 ⟨33,by decide⟩).lower ∧ (cell12701 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12701 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12701 ⟨34,by decide⟩).lower ∧ (cell12701 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12701 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12701 ⟨35,by decide⟩).lower ∧ (cell12701 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12701 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12701 ⟨36,by decide⟩).lower ∧ (cell12701 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12701 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12701 ⟨37,by decide⟩).lower ∧ (cell12701 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12701 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12701 ⟨38,by decide⟩).lower ∧ (cell12701 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12701 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12701 ⟨39,by decide⟩).lower ∧ (cell12701 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12701 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12701 ⟨40,by decide⟩).lower ∧ (cell12701 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12701 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12701 ⟨41,by decide⟩).lower ∧ (cell12701 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12701 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12701 ⟨42,by decide⟩).lower ∧ (cell12701 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12701 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12701 ⟨43,by decide⟩).lower ∧ (cell12701 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12701 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12701 ⟨44,by decide⟩).lower ∧ (cell12701 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12701 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12701 ⟨45,by decide⟩).lower ∧ (cell12701 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12701 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12701 ⟨46,by decide⟩).lower ∧ (cell12701 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12701 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12701 ⟨47,by decide⟩).lower ∧ (cell12701 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12701 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12701 ⟨48,by decide⟩).lower ∧ (cell12701 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12701 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12701 ⟨49,by decide⟩).lower ∧ (cell12701 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12701 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12701 ⟨50,by decide⟩).lower ∧ (cell12701 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12701 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12701 ⟨51,by decide⟩).lower ∧ (cell12701 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12701 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12701 ⟨52,by decide⟩).lower ∧ (cell12701 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12701 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12701 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12701 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12701,cell12701,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12701 i).lower ∧
    (cell12701 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12701 i).upper ≤ (0.532 : ℝ) ∧
    (cell12701 i).centre ≤ (0.1 : ℝ) ∧ (cell12701 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12701 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12701 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12701

/-! The local source numeric instances at 12701 have no network premises. -/
namespace BstLean.Part269.N12701
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12701)
open BstLean.Part268 (cell12701)

noncomputable def sourceNumerics12701 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12701 (cell12701 i)
      scalarRow12701.M scalarRow12701.H scalarRow12701.xi := by
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
    energy_allowance := scalarRow12701.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12701]
    centre_nonneg := (scalarRow12701.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12701])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12701
/-! Actual 12702 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12702
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12702 ≤ (1.035806376921 : ℝ) := by
  have hr : (112.703149911615 : ℝ) ≤ √(12702 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.703149911615 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12702 12702 (11 / 1000) ≤
    (0.008481457965 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12702) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.703149911615 : ℝ) ≤ √(12702 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12702)
  have hdiv : K / √(12702 : ℝ) ≤ K / 112.703149911615 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.703149911615 ≤ (0.008481457965 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12702.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12702 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12702 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12702 := gPlus_lower 12702
end BstLean.Part269.N12702

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12702
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035806376920 : ℝ) ≤ wn 12702 := by
  have hn : √(12702 : ℝ) ≤ 112.703149911616 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12702 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.703149911616 ≤ 2 / √(12702 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251840517 : ℝ) ≤ rhoBar 12702 BstLean.Part154.csC ∧
    rhoBar 12702 BstLean.Part154.csC ≤ 0.000251840907 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035806376920 : ℝ) / (1.295212 * 12702) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035806376921 : ℝ) / (1.29521 * 12702) := by gcongr
      _ ≤ (0.000251840907 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12702 BstLean.Part154.csC) ≤ 0.001007427052 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12702 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12702 BstLean.Part154.csC) (piBar (rhoBar 12702 BstLean.Part154.csC)) ≤ 0.000192357782 ∧
    cc1 (rhoBar 12702 BstLean.Part154.csC) (piBar (rhoBar 12702 BstLean.Part154.csC)) ≤ 0.000122398534 ∧
    cc2 (rhoBar 12702 BstLean.Part154.csC) ≤ 0.000071053287 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12702 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12702 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12702 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12702 BstLean.Part154.csC * nuR (rhoBar 12702 BstLean.Part154.csC)) ≤ 0.000503697670 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251840907 : ℝ) * 0.001007427052 := by gcongr
      _ ≤ (0.000503697670 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12702 BstLean.Part154.csC) * nuR (rhoBar 12702 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001007427052 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12702 BstLean.Part154.csC) * rhoBar 12702 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251840907 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251840907 / 2 + 0.399 * 0.001007427052 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192357782 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503697670 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122398534 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251840907 / 1.414213562 := by gcongr
      _ ≤ (0.000071053287 : ℝ) := by norm_num

end BstLean.Part269.N12702

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12702
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12702 BstLean.Part154.csC) (piBar (rhoBar 12702 BstLean.Part154.csC)) ≤ 1.59792E-7 := by
  have hr0 : 0 ≤ rhoBar 12702 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12702 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12702 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12702 BstLean.Part154.csC) (piBar (rhoBar 12702 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12702 BstLean.Part154.csC) (piBar (rhoBar 12702 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12702 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192357782 : ℝ) ^ 2 + 0.000122398534 ^ 2 + 3 * 0.000071053287 ^ 2 +
        2 * 0.797885 * 0.000192357782 * 0.000122398534 + 2 * 0.000192357782 * 0.000071053287 +
        4 * 0.797885 * 0.000122398534 * 0.000071053287 := by gcongr
    _ ≤ (1.59792E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12702 BstLean.Part154.csC Θ ≤ 0.002628863291 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12702 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12702 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12702 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12702 BstLean.Part154.csC) (piBar (rhoBar 12702 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12702 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035806376921 * 1.59792E-7 / (0.000251840517 : ℝ) := by gcongr
    _ ≤ 0.002628863291 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12702 BstLean.Part154.csC Θ ≤ 0.002916854595 + 0.000664270644 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12702 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12702 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12702 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035806376921 : ℝ) * ((2 * Θ * 0.000251840907 +
        (6863 / 10000) * 0.000251840907 * 12702 * 0.001007427052) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002916854595 + 0.000664270644 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12702 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12702 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12702 0.011 Θ ∧ gammaRatio 12702 0.011 Θ ≤ 0.000086576392 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12702 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035806376921 : ℝ) * 0.525 / ((1 - 0.011) * 12702) := by gcongr
      _ ≤ (0.000086576392 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12702 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12702 0.011 Θ) :=
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
    badAllowance 12702 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12702 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12702 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12702 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12702 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12702 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12702 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12702 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12702 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12702 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12702 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035806376921 : ℝ) * 12702 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12702 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003532547072 + 0.003293133935 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12702

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12702
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12702 BstLean.Part154.csC) (piBar (rhoBar 12702 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12702 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12702 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12702 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12702 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12702 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12702 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12702 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12702 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12702 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12702 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12702 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12702 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12702 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12702 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052480135861 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12702) ≤ 0.010596310592 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12702 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035806376921)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010596310592 + 2 * 0.737676 / 12702) := by gcongr
    _ ≤ (0.052480135861 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12702 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12702

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12702
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503658723 : ℝ) ≤ plow 12702 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12702) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052768042388)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380153228) : eMP 12702 0.011 xi bn ≤ 0.001188186956 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12702 : ℝ) * (1 - 0.011))) ≤ 0.000587495323 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001380153228 / (12702 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587495323 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587495323 : ℝ) + 3.141593 * 0.052768042388 / (12702 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001188186956 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052768042388)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380153228) : PiBarMP 12702 12 0.011 xi bn ≤ 0.161238273403 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12702 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037150413565 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.081568511508 : ℝ) ≤ √((12702 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.703149911615 : ℝ) ≤ √(12702 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12702) ≤ 0.123620398132 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037150413565 + 0.052768042388 * 1.772454 / (2 * (112.081568511508 : ℝ))) * (1 + 0.001188186956) +
        8 / (12702 * 112.703149911615) + 0.123620398132 := by gcongr
    _ ≤ (0.161238273403 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052768042388)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380153228) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282193092370) :
    parallelOracle 12702 0.011 xi bn cd ≤ 0.162228713666 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12702 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12702 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503658723 : ℝ) ≤ plow 12702 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.703149911615 : ℝ) ≤ √(12702 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282193092370 : ℝ) / (2 * 0.560503658723 * 112.703149911615)) * 0.161238273403 +
        0.282193092370 ^ 2 / (2 * 0.560503658723 * 112.703149911615) := by gcongr
    _ ≤ (0.162228713666 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052768042388) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380153228)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282193092370) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12702 12702 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503658723 : ℝ) ≤ plow 12702 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.703149911615 : ℝ) ≤ √(12702 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12702 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12702 Θ 1.22 ≤ 0.011766312664 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.703149911615 := by gcongr <;> linarith
      _ ≤ (0.011766312664 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12702 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12702 12702 0.011 ≤ 0.008481457965 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12702 12702 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12702 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12702 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12702 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12702 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162228713666 + 0.011766312664 + (0.008481457965 : ℝ) *
        (1 + 2 * (0.282193092370 + 0.011766312664) / (0.560503658723 * 112.703149911615))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12702]

end BstLean.Part269.N12702

/-! The original eight local profiles supply actual 12702 moment certificates. -/
namespace BstLean.Part269.N12702
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12702 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12702 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12702 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052768042388 ∧
    0 ≤ bN 12702 BstLean.Part154.csC (groupTheta g) ∧ bN 12702 BstLean.Part154.csC (groupTheta g) ≤ 0.001380153228 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12702 12702 0.011
      (momentAllowance 12702 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12702 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12702 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12702 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12702 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12702 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229712956509 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12702 0.011
      (momentAllowance 12702 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12702 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12702
/-! The actual computed-centre upper energy formula at 12702. -/
namespace BstLean.Part269.N12702
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12702

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12702
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12702)
open BstLean.Part268 (cell12702)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085484425788
  | 2 => 0.086427067985
  | 3 => 0.087367834199
  | 4 => 0.088308138894
  | 5 => 0.089249693062
  | 6 => 0.090194548277
  | 7 => 0.091145144911
  | 8 => 0.092104364522
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12702 12702 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12702 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003533030491 + 0.003293667169 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S14.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12702

/-! Actual upper energy certificates on all 43 source endpoints at 12702. -/
namespace BstLean.Part269.N12702
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12702)
open BstLean.Part268 (cell12702)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12702 (gMinus 12702) (1 - (cell12702 i).lower) ≤ 1 ∧
    energyUpper 12702 (gMinus 12702) (BstLean.Part211.gPlus 12702)
      (finiteEnergy 12702 12702 0.011) (1 - (cell12702 i).lower) ≤
      (cell12702 i).energy := by
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨10,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨11,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨12,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨13,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨14,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨15,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨16,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨17,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨18,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨19,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨20,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨21,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨22,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨23,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨24,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨25,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨26,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨27,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨28,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨29,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨30,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨31,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨32,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨33,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨34,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨35,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨36,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨37,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨38,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨39,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨40,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨41,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨42,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨43,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨44,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨45,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨46,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨47,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨48,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨49,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨50,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨51,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12702) (by norm_num)
        (q := 1 - (cell12702 ⟨52,by decide⟩).lower)
        (by norm_num [cell12702]) (by norm_num [cell12702])
      exact ⟨E.1,E.2.trans (by norm_num [cell12702])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12702

/-! Source-cell containment and simple scalar guards at 12702. -/
namespace BstLean.Part269.N12702
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12702)
open BstLean.Part268 (cell12702)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12702 ⟨10,by decide⟩).lower ∧ (cell12702 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12702 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12702 ⟨11,by decide⟩).lower ∧ (cell12702 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12702 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12702 ⟨12,by decide⟩).lower ∧ (cell12702 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12702 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12702 ⟨13,by decide⟩).lower ∧ (cell12702 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12702 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12702 ⟨14,by decide⟩).lower ∧ (cell12702 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12702 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12702 ⟨15,by decide⟩).lower ∧ (cell12702 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12702 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12702 ⟨16,by decide⟩).lower ∧ (cell12702 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12702 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12702 ⟨17,by decide⟩).lower ∧ (cell12702 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12702 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12702 ⟨18,by decide⟩).lower ∧ (cell12702 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12702 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12702 ⟨19,by decide⟩).lower ∧ (cell12702 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12702 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12702 ⟨20,by decide⟩).lower ∧ (cell12702 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12702 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12702 ⟨21,by decide⟩).lower ∧ (cell12702 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12702 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12702 ⟨22,by decide⟩).lower ∧ (cell12702 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12702 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12702 ⟨23,by decide⟩).lower ∧ (cell12702 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12702 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12702 ⟨24,by decide⟩).lower ∧ (cell12702 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12702 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12702 ⟨25,by decide⟩).lower ∧ (cell12702 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12702 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12702 ⟨26,by decide⟩).lower ∧ (cell12702 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12702 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12702 ⟨27,by decide⟩).lower ∧ (cell12702 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12702 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12702 ⟨28,by decide⟩).lower ∧ (cell12702 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12702 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12702 ⟨29,by decide⟩).lower ∧ (cell12702 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12702 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12702 ⟨30,by decide⟩).lower ∧ (cell12702 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12702 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12702 ⟨31,by decide⟩).lower ∧ (cell12702 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12702 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12702 ⟨32,by decide⟩).lower ∧ (cell12702 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12702 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12702 ⟨33,by decide⟩).lower ∧ (cell12702 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12702 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12702 ⟨34,by decide⟩).lower ∧ (cell12702 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12702 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12702 ⟨35,by decide⟩).lower ∧ (cell12702 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12702 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12702 ⟨36,by decide⟩).lower ∧ (cell12702 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12702 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12702 ⟨37,by decide⟩).lower ∧ (cell12702 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12702 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12702 ⟨38,by decide⟩).lower ∧ (cell12702 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12702 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12702 ⟨39,by decide⟩).lower ∧ (cell12702 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12702 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12702 ⟨40,by decide⟩).lower ∧ (cell12702 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12702 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12702 ⟨41,by decide⟩).lower ∧ (cell12702 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12702 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12702 ⟨42,by decide⟩).lower ∧ (cell12702 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12702 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12702 ⟨43,by decide⟩).lower ∧ (cell12702 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12702 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12702 ⟨44,by decide⟩).lower ∧ (cell12702 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12702 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12702 ⟨45,by decide⟩).lower ∧ (cell12702 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12702 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12702 ⟨46,by decide⟩).lower ∧ (cell12702 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12702 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12702 ⟨47,by decide⟩).lower ∧ (cell12702 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12702 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12702 ⟨48,by decide⟩).lower ∧ (cell12702 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12702 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12702 ⟨49,by decide⟩).lower ∧ (cell12702 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12702 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12702 ⟨50,by decide⟩).lower ∧ (cell12702 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12702 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12702 ⟨51,by decide⟩).lower ∧ (cell12702 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12702 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12702 ⟨52,by decide⟩).lower ∧ (cell12702 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12702 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12702 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12702 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12702,cell12702,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12702 i).lower ∧
    (cell12702 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12702 i).upper ≤ (0.532 : ℝ) ∧
    (cell12702 i).centre ≤ (0.1 : ℝ) ∧ (cell12702 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12702 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12702 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12702

/-! The local source numeric instances at 12702 have no network premises. -/
namespace BstLean.Part269.N12702
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12702)
open BstLean.Part268 (cell12702)

noncomputable def sourceNumerics12702 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12702 (cell12702 i)
      scalarRow12702.M scalarRow12702.H scalarRow12702.xi := by
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
    energy_allowance := scalarRow12702.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12702]
    centre_nonneg := (scalarRow12702.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12702])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12702
/-! Actual 12703 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12703
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12703 ≤ (1.035804955132 : ℝ) := by
  have hr : (112.707586257536 : ℝ) ≤ √(12703 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.707586257536 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12703 12703 (11 / 1000) ≤
    (0.008481124119 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12703) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.707586257536 : ℝ) ≤ √(12703 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12703)
  have hdiv : K / √(12703 : ℝ) ≤ K / 112.707586257536 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.707586257536 ≤ (0.008481124119 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12703.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12703 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12703 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12703 := gPlus_lower 12703
end BstLean.Part269.N12703

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12703
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035804955131 : ℝ) ≤ wn 12703 := by
  have hn : √(12703 : ℝ) ≤ 112.707586257537 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12703 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.707586257537 ≤ 2 / √(12703 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251820347 : ℝ) ≤ rhoBar 12703 BstLean.Part154.csC ∧
    rhoBar 12703 BstLean.Part154.csC ≤ 0.000251820736 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035804955131 : ℝ) / (1.295212 * 12703) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035804955132 : ℝ) / (1.29521 * 12703) := by gcongr
      _ ≤ (0.000251820736 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12703 BstLean.Part154.csC) ≤ 0.001007346358 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12703 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12703 BstLean.Part154.csC) (piBar (rhoBar 12703 BstLean.Part154.csC)) ≤ 0.000192342375 ∧
    cc1 (rhoBar 12703 BstLean.Part154.csC) (piBar (rhoBar 12703 BstLean.Part154.csC)) ≤ 0.000122388731 ∧
    cc2 (rhoBar 12703 BstLean.Part154.csC) ≤ 0.000071047596 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12703 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12703 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12703 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12703 BstLean.Part154.csC * nuR (rhoBar 12703 BstLean.Part154.csC)) ≤ 0.000503657326 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251820736 : ℝ) * 0.001007346358 := by gcongr
      _ ≤ (0.000503657326 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12703 BstLean.Part154.csC) * nuR (rhoBar 12703 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001007346358 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12703 BstLean.Part154.csC) * rhoBar 12703 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251820736 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251820736 / 2 + 0.399 * 0.001007346358 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192342375 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503657326 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122388731 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251820736 / 1.414213562 := by gcongr
      _ ≤ (0.000071047596 : ℝ) := by norm_num

end BstLean.Part269.N12703

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12703
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12703 BstLean.Part154.csC) (piBar (rhoBar 12703 BstLean.Part154.csC)) ≤ 1.59766E-7 := by
  have hr0 : 0 ≤ rhoBar 12703 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12703 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12703 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12703 BstLean.Part154.csC) (piBar (rhoBar 12703 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12703 BstLean.Part154.csC) (piBar (rhoBar 12703 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12703 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192342375 : ℝ) ^ 2 + 0.000122388731 ^ 2 + 3 * 0.000071047596 ^ 2 +
        2 * 0.797885 * 0.000192342375 * 0.000122388731 + 2 * 0.000192342375 * 0.000071047596 +
        4 * 0.797885 * 0.000122388731 * 0.000071047596 := by gcongr
    _ ≤ (1.59766E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12703 BstLean.Part154.csC Θ ≤ 0.002628642466 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12703 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12703 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12703 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12703 BstLean.Part154.csC) (piBar (rhoBar 12703 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12703 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035804955132 * 1.59766E-7 / (0.000251820347 : ℝ) := by gcongr
    _ ≤ 0.002628642466 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12703 BstLean.Part154.csC Θ ≤ 0.002916612951 + 0.000664216528 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12703 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12703 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12703 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035804955132 : ℝ) * ((2 * Θ * 0.000251820736 +
        (6863 / 10000) * 0.000251820736 * 12703 * 0.001007346358) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002916612951 + 0.000664216528 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12703 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12703 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12703 0.011 Θ ∧ gammaRatio 12703 0.011 Θ ≤ 0.000086569458 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12703 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035804955132 : ℝ) * 0.525 / ((1 - 0.011) * 12703) := by gcongr
      _ ≤ (0.000086569458 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12703 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12703 0.011 Θ) :=
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
    badAllowance 12703 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12703 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12703 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12703 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12703 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12703 0.011 Θ) 1.12 ≤ 2.7751E-8 := by
    have he : (17.4 : ℝ) ≤ gap 1 (gammaRatio 12703 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12703 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12703 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_4_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12703 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12703 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035804955132 : ℝ) * 12703 *
        (2.2721E-8 / 1.1045361 + 2.7751E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12703 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003532305428 + 0.003292858994 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12703

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12703
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12703 BstLean.Part154.csC) (piBar (rhoBar 12703 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12703 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12703 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12703 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12703 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12703 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12703 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12703 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12703 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12703 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12703 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12703 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12703 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12703 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12703 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052478047761 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12703) ≤ 0.010595893504 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12703 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035804955132)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010595893504 + 2 * 0.737676 / 12703) := by gcongr
    _ ≤ (0.052478047761 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12703 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12703

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12703
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503703928 : ℝ) ≤ plow 12703 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12703) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052767656400)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380037295) : eMP 12703 0.011 xi bn ≤ 0.001188090223 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12703 : ℝ) * (1 - 0.011))) ≤ 0.000587447524 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001380037295 / (12703 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587447524 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587447524 : ℝ) + 3.141593 * 0.052767656400 / (12703 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001188090223 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052767656400)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380037295) : PiBarMP 12703 12 0.011 xi bn ≤ 0.161231821514 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12703 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037148853213 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.085980390055 : ℝ) ≤ √((12703 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.707586257536 : ℝ) ≤ √(12703 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12703) ≤ 0.123615532241 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037148853213 + 0.052767656400 * 1.772454 / (2 * (112.085980390055 : ℝ))) * (1 + 0.001188090223) +
        8 / (12703 * 112.707586257536) + 0.123615532241 := by gcongr
    _ ≤ (0.161231821514 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052767656400)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380037295) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282190164116) :
    parallelOracle 12703 0.011 xi bn cd ≤ 0.162222191484 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12703 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12703 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503703928 : ℝ) ≤ plow 12703 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.707586257536 : ℝ) ≤ √(12703 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282190164116 : ℝ) / (2 * 0.560503703928 * 112.707586257536)) * 0.161231821514 +
        0.282190164116 ^ 2 / (2 * 0.560503703928 * 112.707586257536) := by gcongr
    _ ≤ (0.162222191484 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052767656400) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001380037295)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282190164116) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12703 12703 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503703928 : ℝ) ≤ plow 12703 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.707586257536 : ℝ) ≤ √(12703 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12703 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12703 Θ 1.22 ≤ 0.011765849523 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.707586257536 := by gcongr <;> linarith
      _ ≤ (0.011765849523 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12703 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12703 12703 0.011 ≤ 0.008481124119 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12703 12703 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12703 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12703 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12703 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12703 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162222191484 + 0.011765849523 + (0.008481124119 : ℝ) *
        (1 + 2 * (0.282190164116 + 0.011765849523) / (0.560503703928 * 112.707586257536))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12703]

end BstLean.Part269.N12703

/-! The original eight local profiles supply actual 12703 moment certificates. -/
namespace BstLean.Part269.N12703
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12703 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12703 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12703 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052767656400 ∧
    0 ≤ bN 12703 BstLean.Part154.csC (groupTheta g) ∧ bN 12703 BstLean.Part154.csC (groupTheta g) ≤ 0.001380037295 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12703 12703 0.011
      (momentAllowance 12703 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12703 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12703 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12703 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12703 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12703 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229712116355 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12703 0.011
      (momentAllowance 12703 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12703 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12703
/-! The actual computed-centre upper energy formula at 12703. -/
namespace BstLean.Part269.N12703
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12703

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12703
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12703)
open BstLean.Part268 (cell12703)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085481512200
  | 2 => 0.086424100929
  | 3 => 0.087364805885
  | 4 => 0.088305039738
  | 5 => 0.089246511365
  | 6 => 0.090191269873
  | 7 => 0.091141752766
  | 8 => 0.092100838294
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12703 12703 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12703 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003533030491 + 0.003293667169 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S14.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12703

/-! Actual upper energy certificates on all 43 source endpoints at 12703. -/
namespace BstLean.Part269.N12703
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12703)
open BstLean.Part268 (cell12703)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12703 (gMinus 12703) (1 - (cell12703 i).lower) ≤ 1 ∧
    energyUpper 12703 (gMinus 12703) (BstLean.Part211.gPlus 12703)
      (finiteEnergy 12703 12703 0.011) (1 - (cell12703 i).lower) ≤
      (cell12703 i).energy := by
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨10,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨11,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨12,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨13,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨14,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨15,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨16,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨17,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨18,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨19,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨20,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨21,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨22,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨23,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨24,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨25,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨26,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨27,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨28,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨29,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨30,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨31,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨32,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨33,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨34,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨35,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨36,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨37,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨38,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨39,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨40,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨41,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨42,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨43,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨44,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨45,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨46,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨47,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨48,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨49,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨50,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨51,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12703) (by norm_num)
        (q := 1 - (cell12703 ⟨52,by decide⟩).lower)
        (by norm_num [cell12703]) (by norm_num [cell12703])
      exact ⟨E.1,E.2.trans (by norm_num [cell12703])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12703

/-! Source-cell containment and simple scalar guards at 12703. -/
namespace BstLean.Part269.N12703
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12703)
open BstLean.Part268 (cell12703)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12703 ⟨10,by decide⟩).lower ∧ (cell12703 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12703 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12703 ⟨11,by decide⟩).lower ∧ (cell12703 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12703 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12703 ⟨12,by decide⟩).lower ∧ (cell12703 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12703 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12703 ⟨13,by decide⟩).lower ∧ (cell12703 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12703 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12703 ⟨14,by decide⟩).lower ∧ (cell12703 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12703 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12703 ⟨15,by decide⟩).lower ∧ (cell12703 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12703 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12703 ⟨16,by decide⟩).lower ∧ (cell12703 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12703 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12703 ⟨17,by decide⟩).lower ∧ (cell12703 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12703 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12703 ⟨18,by decide⟩).lower ∧ (cell12703 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12703 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12703 ⟨19,by decide⟩).lower ∧ (cell12703 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12703 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12703 ⟨20,by decide⟩).lower ∧ (cell12703 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12703 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12703 ⟨21,by decide⟩).lower ∧ (cell12703 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12703 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12703 ⟨22,by decide⟩).lower ∧ (cell12703 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12703 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12703 ⟨23,by decide⟩).lower ∧ (cell12703 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12703 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12703 ⟨24,by decide⟩).lower ∧ (cell12703 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12703 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12703 ⟨25,by decide⟩).lower ∧ (cell12703 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12703 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12703 ⟨26,by decide⟩).lower ∧ (cell12703 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12703 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12703 ⟨27,by decide⟩).lower ∧ (cell12703 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12703 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12703 ⟨28,by decide⟩).lower ∧ (cell12703 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12703 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12703 ⟨29,by decide⟩).lower ∧ (cell12703 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12703 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12703 ⟨30,by decide⟩).lower ∧ (cell12703 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12703 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12703 ⟨31,by decide⟩).lower ∧ (cell12703 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12703 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12703 ⟨32,by decide⟩).lower ∧ (cell12703 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12703 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12703 ⟨33,by decide⟩).lower ∧ (cell12703 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12703 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12703 ⟨34,by decide⟩).lower ∧ (cell12703 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12703 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12703 ⟨35,by decide⟩).lower ∧ (cell12703 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12703 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12703 ⟨36,by decide⟩).lower ∧ (cell12703 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12703 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12703 ⟨37,by decide⟩).lower ∧ (cell12703 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12703 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12703 ⟨38,by decide⟩).lower ∧ (cell12703 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12703 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12703 ⟨39,by decide⟩).lower ∧ (cell12703 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12703 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12703 ⟨40,by decide⟩).lower ∧ (cell12703 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12703 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12703 ⟨41,by decide⟩).lower ∧ (cell12703 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12703 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12703 ⟨42,by decide⟩).lower ∧ (cell12703 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12703 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12703 ⟨43,by decide⟩).lower ∧ (cell12703 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12703 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12703 ⟨44,by decide⟩).lower ∧ (cell12703 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12703 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12703 ⟨45,by decide⟩).lower ∧ (cell12703 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12703 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12703 ⟨46,by decide⟩).lower ∧ (cell12703 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12703 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12703 ⟨47,by decide⟩).lower ∧ (cell12703 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12703 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12703 ⟨48,by decide⟩).lower ∧ (cell12703 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12703 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12703 ⟨49,by decide⟩).lower ∧ (cell12703 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12703 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12703 ⟨50,by decide⟩).lower ∧ (cell12703 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12703 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12703 ⟨51,by decide⟩).lower ∧ (cell12703 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12703 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12703 ⟨52,by decide⟩).lower ∧ (cell12703 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12703 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12703 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12703 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12703,cell12703,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12703 i).lower ∧
    (cell12703 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12703 i).upper ≤ (0.532 : ℝ) ∧
    (cell12703 i).centre ≤ (0.1 : ℝ) ∧ (cell12703 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12703 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12703 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12703

/-! The local source numeric instances at 12703 have no network premises. -/
namespace BstLean.Part269.N12703
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12703)
open BstLean.Part268 (cell12703)

noncomputable def sourceNumerics12703 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12703 (cell12703 i)
      scalarRow12703.M scalarRow12703.H scalarRow12703.xi := by
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
    energy_allowance := scalarRow12703.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12703]
    centre_nonneg := (scalarRow12703.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12703])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12703
/-! Actual 12704 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12704
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12704 ≤ (1.035803533511 : ℝ) := by
  have hr : (112.712022428842 : ℝ) ≤ √(12704 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.712022428842 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12704 12704 (11 / 1000) ≤
    (0.008480790313 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12704) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.712022428842 : ℝ) ≤ √(12704 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12704)
  have hdiv : K / √(12704 : ℝ) ≤ K / 112.712022428842 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.712022428842 ≤ (0.008480790313 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12704.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12704 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12704 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12704 := gPlus_lower 12704
end BstLean.Part269.N12704

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12704
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035803533510 : ℝ) ≤ wn 12704 := by
  have hn : √(12704 : ℝ) ≤ 112.712022428843 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12704 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.712022428843 ≤ 2 / √(12704 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251800179 : ℝ) ≤ rhoBar 12704 BstLean.Part154.csC ∧
    rhoBar 12704 BstLean.Part154.csC ≤ 0.000251800569 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035803533510 : ℝ) / (1.295212 * 12704) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035803533511 : ℝ) / (1.29521 * 12704) := by gcongr
      _ ≤ (0.000251800569 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12704 BstLean.Part154.csC) ≤ 0.001007265680 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12704 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12704 BstLean.Part154.csC) (piBar (rhoBar 12704 BstLean.Part154.csC)) ≤ 0.000192326970 ∧
    cc1 (rhoBar 12704 BstLean.Part154.csC) (piBar (rhoBar 12704 BstLean.Part154.csC)) ≤ 0.000122378929 ∧
    cc2 (rhoBar 12704 BstLean.Part154.csC) ≤ 0.000071041907 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12704 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12704 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12704 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12704 BstLean.Part154.csC * nuR (rhoBar 12704 BstLean.Part154.csC)) ≤ 0.000503616989 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251800569 : ℝ) * 0.001007265680 := by gcongr
      _ ≤ (0.000503616989 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12704 BstLean.Part154.csC) * nuR (rhoBar 12704 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001007265680 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12704 BstLean.Part154.csC) * rhoBar 12704 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251800569 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251800569 / 2 + 0.399 * 0.001007265680 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192326970 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503616989 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122378929 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251800569 / 1.414213562 := by gcongr
      _ ≤ (0.000071041907 : ℝ) := by norm_num

end BstLean.Part269.N12704

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12704
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12704 BstLean.Part154.csC) (piBar (rhoBar 12704 BstLean.Part154.csC)) ≤ 1.59741E-7 := by
  have hr0 : 0 ≤ rhoBar 12704 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12704 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12704 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12704 BstLean.Part154.csC) (piBar (rhoBar 12704 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12704 BstLean.Part154.csC) (piBar (rhoBar 12704 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12704 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192326970 : ℝ) ^ 2 + 0.000122378929 ^ 2 + 3 * 0.000071041907 ^ 2 +
        2 * 0.797885 * 0.000192326970 * 0.000122378929 + 2 * 0.000192326970 * 0.000071041907 +
        4 * 0.797885 * 0.000122378929 * 0.000071041907 := by gcongr
    _ ≤ (1.59741E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12704 BstLean.Part154.csC Θ ≤ 0.002628438041 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12704 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12704 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12704 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12704 BstLean.Part154.csC) (piBar (rhoBar 12704 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12704 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035803533511 * 1.59741E-7 / (0.000251800179 : ℝ) := by gcongr
    _ ≤ 0.002628438041 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12704 BstLean.Part154.csC Θ ≤ 0.002916371363 + 0.000664162423 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12704 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12704 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12704 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035803533511 : ℝ) * ((2 * Θ * 0.000251800569 +
        (6863 / 10000) * 0.000251800569 * 12704 * 0.001007265680) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002916371363 + 0.000664162423 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12704 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12704 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12704 0.011 Θ ∧ gammaRatio 12704 0.011 Θ ≤ 0.000086562524 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12704 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035803533511 : ℝ) * 0.525 / ((1 - 0.011) * 12704) := by gcongr
      _ ≤ (0.000086562524 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12704 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12704 0.011 Θ) :=
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
    badAllowance 12704 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12704 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12704 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12704 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12704 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12704 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12704 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12704 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12704 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12704 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12704 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035803533511 : ℝ) * 12704 *
        (2.2721E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12704 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003532063840 + 0.003292600464 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12704

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12704
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12704 BstLean.Part154.csC) (piBar (rhoBar 12704 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12704 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12704 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12704 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12704 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12704 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12704 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12704 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12704 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12704 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12704 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12704 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12704 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12704 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12704 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052475959913 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12704) ≤ 0.010595476466 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12704 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035803533511)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010595476466 + 2 * 0.737676 / 12704) := by gcongr
    _ ≤ (0.052475959913 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12704 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12704

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12704
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503749126 : ℝ) ≤ plow 12704 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12704) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052767279084)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379929972) : eMP 12704 0.011 xi bn ≤ 0.001187997164 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12704 : ℝ) * (1 - 0.011))) ≤ 0.000587401561 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001379929972 / (12704 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587401561 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587401561 : ℝ) + 3.141593 * 0.052767279084 / (12704 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001187997164 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052767279084)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379929972) : PiBarMP 12704 12 0.011 xi bn ≤ 0.161225486370 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12704 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037147408685 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.090392094951 : ℝ) ≤ √((12704 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.712022428842 : ℝ) ≤ √(12704 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12704) ≤ 0.123610666924 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037147408685 + 0.052767279084 * 1.772454 / (2 * (112.090392094951 : ℝ))) * (1 + 0.001187997164) +
        8 / (12704 * 112.712022428842) + 0.123610666924 := by gcongr
    _ ≤ (0.161225486370 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052767279084)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379929972) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282187254986) :
    parallelOracle 12704 0.011 xi bn cd ≤ 0.162215786425 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12704 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12704 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503749126 : ℝ) ≤ plow 12704 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.712022428842 : ℝ) ≤ √(12704 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282187254986 : ℝ) / (2 * 0.560503749126 * 112.712022428842)) * 0.161225486370 +
        0.282187254986 ^ 2 / (2 * 0.560503749126 * 112.712022428842) := by gcongr
    _ ≤ (0.162215786425 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052767279084) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379929972)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282187254986) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12704 12704 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503749126 : ℝ) ≤ plow 12704 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.712022428842 : ℝ) ≤ √(12704 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12704 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12704 Θ 1.22 ≤ 0.011765386438 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.712022428842 := by gcongr <;> linarith
      _ ≤ (0.011765386438 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12704 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12704 12704 0.011 ≤ 0.008480790313 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12704 12704 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12704 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12704 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12704 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12704 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162215786425 + 0.011765386438 + (0.008480790313 : ℝ) *
        (1 + 2 * (0.282187254986 + 0.011765386438) / (0.560503749126 * 112.712022428842))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12704]

end BstLean.Part269.N12704

/-! The original eight local profiles supply actual 12704 moment certificates. -/
namespace BstLean.Part269.N12704
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12704 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12704 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12704 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052767279084 ∧
    0 ≤ bN 12704 BstLean.Part154.csC (groupTheta g) ∧ bN 12704 BstLean.Part154.csC (groupTheta g) ≤ 0.001379929972 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12704 12704 0.011
      (momentAllowance 12704 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12704 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12704 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12704 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12704 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12704 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229711295073 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12704 0.011
      (momentAllowance 12704 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12704 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12704
/-! The actual computed-centre upper energy formula at 12704. -/
namespace BstLean.Part269.N12704
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12704

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12704
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12704)
open BstLean.Part268 (cell12704)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085478599693
  | 2 => 0.086421134998
  | 3 => 0.087361778752
  | 4 => 0.088301941829
  | 5 => 0.089243330997
  | 6 => 0.090187992898
  | 7 => 0.091138362171
  | 8 => 0.092097313762
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12704 12704 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12704 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003533030491 + 0.003293667169 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S14.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12704

/-! Actual upper energy certificates on all 43 source endpoints at 12704. -/
namespace BstLean.Part269.N12704
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12704)
open BstLean.Part268 (cell12704)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12704 (gMinus 12704) (1 - (cell12704 i).lower) ≤ 1 ∧
    energyUpper 12704 (gMinus 12704) (BstLean.Part211.gPlus 12704)
      (finiteEnergy 12704 12704 0.011) (1 - (cell12704 i).lower) ≤
      (cell12704 i).energy := by
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨10,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨11,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨12,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨13,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨14,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨15,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨16,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨17,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨18,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨19,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨20,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨21,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨22,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨23,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨24,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨25,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨26,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨27,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨28,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨29,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨30,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨31,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨32,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨33,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨34,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨35,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨36,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨37,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨38,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨39,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨40,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨41,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨42,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨43,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨44,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨45,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨46,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨47,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨48,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨49,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨50,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨51,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12704) (by norm_num)
        (q := 1 - (cell12704 ⟨52,by decide⟩).lower)
        (by norm_num [cell12704]) (by norm_num [cell12704])
      exact ⟨E.1,E.2.trans (by norm_num [cell12704])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12704

/-! Source-cell containment and simple scalar guards at 12704. -/
namespace BstLean.Part269.N12704
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12704)
open BstLean.Part268 (cell12704)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12704 ⟨10,by decide⟩).lower ∧ (cell12704 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12704 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12704 ⟨11,by decide⟩).lower ∧ (cell12704 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12704 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12704 ⟨12,by decide⟩).lower ∧ (cell12704 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12704 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12704 ⟨13,by decide⟩).lower ∧ (cell12704 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12704 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12704 ⟨14,by decide⟩).lower ∧ (cell12704 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12704 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12704 ⟨15,by decide⟩).lower ∧ (cell12704 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12704 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12704 ⟨16,by decide⟩).lower ∧ (cell12704 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12704 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12704 ⟨17,by decide⟩).lower ∧ (cell12704 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12704 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12704 ⟨18,by decide⟩).lower ∧ (cell12704 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12704 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12704 ⟨19,by decide⟩).lower ∧ (cell12704 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12704 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12704 ⟨20,by decide⟩).lower ∧ (cell12704 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12704 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12704 ⟨21,by decide⟩).lower ∧ (cell12704 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12704 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12704 ⟨22,by decide⟩).lower ∧ (cell12704 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12704 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12704 ⟨23,by decide⟩).lower ∧ (cell12704 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12704 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12704 ⟨24,by decide⟩).lower ∧ (cell12704 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12704 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12704 ⟨25,by decide⟩).lower ∧ (cell12704 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12704 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12704 ⟨26,by decide⟩).lower ∧ (cell12704 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12704 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12704 ⟨27,by decide⟩).lower ∧ (cell12704 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12704 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12704 ⟨28,by decide⟩).lower ∧ (cell12704 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12704 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12704 ⟨29,by decide⟩).lower ∧ (cell12704 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12704 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12704 ⟨30,by decide⟩).lower ∧ (cell12704 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12704 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12704 ⟨31,by decide⟩).lower ∧ (cell12704 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12704 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12704 ⟨32,by decide⟩).lower ∧ (cell12704 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12704 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12704 ⟨33,by decide⟩).lower ∧ (cell12704 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12704 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12704 ⟨34,by decide⟩).lower ∧ (cell12704 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12704 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12704 ⟨35,by decide⟩).lower ∧ (cell12704 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12704 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12704 ⟨36,by decide⟩).lower ∧ (cell12704 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12704 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12704 ⟨37,by decide⟩).lower ∧ (cell12704 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12704 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12704 ⟨38,by decide⟩).lower ∧ (cell12704 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12704 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12704 ⟨39,by decide⟩).lower ∧ (cell12704 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12704 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12704 ⟨40,by decide⟩).lower ∧ (cell12704 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12704 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12704 ⟨41,by decide⟩).lower ∧ (cell12704 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12704 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12704 ⟨42,by decide⟩).lower ∧ (cell12704 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12704 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12704 ⟨43,by decide⟩).lower ∧ (cell12704 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12704 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12704 ⟨44,by decide⟩).lower ∧ (cell12704 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12704 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12704 ⟨45,by decide⟩).lower ∧ (cell12704 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12704 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12704 ⟨46,by decide⟩).lower ∧ (cell12704 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12704 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12704 ⟨47,by decide⟩).lower ∧ (cell12704 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12704 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12704 ⟨48,by decide⟩).lower ∧ (cell12704 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12704 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12704 ⟨49,by decide⟩).lower ∧ (cell12704 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12704 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12704 ⟨50,by decide⟩).lower ∧ (cell12704 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12704 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12704 ⟨51,by decide⟩).lower ∧ (cell12704 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12704 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12704 ⟨52,by decide⟩).lower ∧ (cell12704 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12704 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12704 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12704 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12704,cell12704,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12704 i).lower ∧
    (cell12704 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12704 i).upper ≤ (0.532 : ℝ) ∧
    (cell12704 i).centre ≤ (0.1 : ℝ) ∧ (cell12704 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12704 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12704 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12704

/-! The local source numeric instances at 12704 have no network premises. -/
namespace BstLean.Part269.N12704
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12704)
open BstLean.Part268 (cell12704)

noncomputable def sourceNumerics12704 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12704 (cell12704 i)
      scalarRow12704.M scalarRow12704.H scalarRow12704.xi := by
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
    energy_allowance := scalarRow12704.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12704]
    centre_nonneg := (scalarRow12704.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12704])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12704
/-! Actual 12705 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12705
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12705 ≤ (1.035802112059 : ℝ) := by
  have hr : (112.716458425555 : ℝ) ≤ √(12705 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.716458425555 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12705 12705 (11 / 1000) ≤
    (0.008480456546 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12705) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.716458425555 : ℝ) ≤ √(12705 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12705)
  have hdiv : K / √(12705 : ℝ) ≤ K / 112.716458425555 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.716458425555 ≤ (0.008480456546 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12705.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12705 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12705 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12705 := gPlus_lower 12705
end BstLean.Part269.N12705

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12705
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035802112058 : ℝ) ≤ wn 12705 := by
  have hn : √(12705 : ℝ) ≤ 112.716458425556 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12705 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.716458425556 ≤ 2 / √(12705 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251780014 : ℝ) ≤ rhoBar 12705 BstLean.Part154.csC ∧
    rhoBar 12705 BstLean.Part154.csC ≤ 0.000251780404 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035802112058 : ℝ) / (1.295212 * 12705) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035802112059 : ℝ) / (1.29521 * 12705) := by gcongr
      _ ≤ (0.000251780404 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12705 BstLean.Part154.csC) ≤ 0.001007185010 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12705 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12705 BstLean.Part154.csC) (piBar (rhoBar 12705 BstLean.Part154.csC)) ≤ 0.000192311568 ∧
    cc1 (rhoBar 12705 BstLean.Part154.csC) (piBar (rhoBar 12705 BstLean.Part154.csC)) ≤ 0.000122369128 ∧
    cc2 (rhoBar 12705 BstLean.Part154.csC) ≤ 0.000071036217 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12705 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12705 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12705 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12705 BstLean.Part154.csC * nuR (rhoBar 12705 BstLean.Part154.csC)) ≤ 0.000503576657 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251780404 : ℝ) * 0.001007185010 := by gcongr
      _ ≤ (0.000503576657 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12705 BstLean.Part154.csC) * nuR (rhoBar 12705 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001007185010 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12705 BstLean.Part154.csC) * rhoBar 12705 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251780404 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251780404 / 2 + 0.399 * 0.001007185010 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192311568 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503576657 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122369128 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251780404 / 1.414213562 := by gcongr
      _ ≤ (0.000071036217 : ℝ) := by norm_num

end BstLean.Part269.N12705

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12705
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12705 BstLean.Part154.csC) (piBar (rhoBar 12705 BstLean.Part154.csC)) ≤ 1.59715E-7 := by
  have hr0 : 0 ≤ rhoBar 12705 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12705 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12705 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12705 BstLean.Part154.csC) (piBar (rhoBar 12705 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12705 BstLean.Part154.csC) (piBar (rhoBar 12705 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12705 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192311568 : ℝ) ^ 2 + 0.000122369128 ^ 2 + 3 * 0.000071036217 ^ 2 +
        2 * 0.797885 * 0.000192311568 * 0.000122369128 + 2 * 0.000192311568 * 0.000071036217 +
        4 * 0.797885 * 0.000122369128 * 0.000071036217 := by gcongr
    _ ≤ (1.59715E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12705 BstLean.Part154.csC Θ ≤ 0.002628217097 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12705 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12705 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12705 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12705 BstLean.Part154.csC) (piBar (rhoBar 12705 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12705 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035802112059 * 1.59715E-7 / (0.000251780014 : ℝ) := by gcongr
    _ ≤ 0.002628217097 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12705 BstLean.Part154.csC Θ ≤ 0.002916129788 + 0.000664108323 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12705 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12705 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12705 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035802112059 : ℝ) * ((2 * Θ * 0.000251780404 +
        (6863 / 10000) * 0.000251780404 * 12705 * 0.001007185010) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002916129788 + 0.000664108323 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12705 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12705 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12705 0.011 Θ ∧ gammaRatio 12705 0.011 Θ ≤ 0.000086555592 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12705 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035802112059 : ℝ) * 0.525 / ((1 - 0.011) * 12705) := by gcongr
      _ ≤ (0.000086555592 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12705 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12705 0.011 Θ) :=
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
    badAllowance 12705 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12705 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12705 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12705 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12705 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12705 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12705 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12705 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12705 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12705 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12705 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035802112059 : ℝ) * 12705 *
        (2.2721E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12705 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003531822265 + 0.003292325420 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12705

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12705
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12705 BstLean.Part154.csC) (piBar (rhoBar 12705 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12705 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12705 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12705 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12705 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12705 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12705 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12705 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12705 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12705 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12705 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12705 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12705 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12705 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12705 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052473872312 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12705) ≤ 0.010595059477 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12705 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035802112059)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010595059477 + 2 * 0.737676 / 12705) := by gcongr
    _ ≤ (0.052473872312 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12705 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12705

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12705
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503794317 : ℝ) ≤ plow 12705 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12705) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052766893111)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379813976) : eMP 12705 0.011 xi bn ≤ 0.001187900419 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12705 : ℝ) * (1 - 0.011))) ≤ 0.000587353756 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001379813976 / (12705 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587353756 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587353756 : ℝ) + 3.141593 * 0.052766893111 / (12705 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001187900419 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052766893111)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379813976) : PiBarMP 12705 12 0.011 xi bn ≤ 0.161219034660 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12705 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037145847359 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.094803626216 : ℝ) ≤ √((12705 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.716458425555 : ℝ) ≤ √(12705 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12705) ≤ 0.123605802182 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037145847359 + 0.052766893111 * 1.772454 / (2 * (112.094803626216 : ℝ))) * (1 + 0.001187900419) +
        8 / (12705 * 112.716458425555) + 0.123605802182 := by gcongr
    _ ≤ (0.161219034660 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052766893111)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379813976) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282184327257) :
    parallelOracle 12705 0.011 xi bn cd ≤ 0.162209264441 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12705 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12705 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503794317 : ℝ) ≤ plow 12705 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.716458425555 : ℝ) ≤ √(12705 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282184327257 : ℝ) / (2 * 0.560503794317 * 112.716458425555)) * 0.161219034660 +
        0.282184327257 ^ 2 / (2 * 0.560503794317 * 112.716458425555) := by gcongr
    _ ≤ (0.162209264441 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052766893111) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379813976)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282184327257) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12705 12705 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503794317 : ℝ) ≤ plow 12705 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.716458425555 : ℝ) ≤ √(12705 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12705 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12705 Θ 1.22 ≤ 0.011764923407 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.716458425555 := by gcongr <;> linarith
      _ ≤ (0.011764923407 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12705 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12705 12705 0.011 ≤ 0.008480456546 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12705 12705 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12705 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12705 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12705 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12705 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162209264441 + 0.011764923407 + (0.008480456546 : ℝ) *
        (1 + 2 * (0.282184327257 + 0.011764923407) / (0.560503794317 * 112.716458425555))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12705]

end BstLean.Part269.N12705

/-! The original eight local profiles supply actual 12705 moment certificates. -/
namespace BstLean.Part269.N12705
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12705 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12705 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12705 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052766893111 ∧
    0 ≤ bN 12705 BstLean.Part154.csC (groupTheta g) ∧ bN 12705 BstLean.Part154.csC (groupTheta g) ≤ 0.001379813976 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12705 12705 0.011
      (momentAllowance 12705 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12705 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12705 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12705 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12705 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12705 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229710454945 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12705 0.011
      (momentAllowance 12705 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12705 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12705
/-! The actual computed-centre upper energy formula at 12705. -/
namespace BstLean.Part269.N12705
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12705

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12705
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12705)
open BstLean.Part268 (cell12705)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085475688265
  | 2 => 0.086418170192
  | 3 => 0.087358752797
  | 4 => 0.088298845165
  | 5 => 0.089240151957
  | 6 => 0.090184717351
  | 7 => 0.091134973125
  | 8 => 0.092093790923
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12705 12705 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12705 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003533030491 + 0.003293667169 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S14.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12705

/-! Actual upper energy certificates on all 43 source endpoints at 12705. -/
namespace BstLean.Part269.N12705
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12705)
open BstLean.Part268 (cell12705)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12705 (gMinus 12705) (1 - (cell12705 i).lower) ≤ 1 ∧
    energyUpper 12705 (gMinus 12705) (BstLean.Part211.gPlus 12705)
      (finiteEnergy 12705 12705 0.011) (1 - (cell12705 i).lower) ≤
      (cell12705 i).energy := by
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨10,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨11,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨12,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨13,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨14,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨15,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨16,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨17,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨18,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨19,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨20,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨21,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨22,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨23,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨24,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨25,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨26,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨27,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨28,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨29,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨30,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨31,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨32,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨33,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨34,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨35,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨36,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨37,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨38,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨39,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨40,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨41,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨42,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨43,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨44,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨45,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨46,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨47,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨48,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨49,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨50,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨51,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12705) (by norm_num)
        (q := 1 - (cell12705 ⟨52,by decide⟩).lower)
        (by norm_num [cell12705]) (by norm_num [cell12705])
      exact ⟨E.1,E.2.trans (by norm_num [cell12705])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12705

/-! Source-cell containment and simple scalar guards at 12705. -/
namespace BstLean.Part269.N12705
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12705)
open BstLean.Part268 (cell12705)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12705 ⟨10,by decide⟩).lower ∧ (cell12705 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12705 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12705 ⟨11,by decide⟩).lower ∧ (cell12705 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12705 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12705 ⟨12,by decide⟩).lower ∧ (cell12705 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12705 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12705 ⟨13,by decide⟩).lower ∧ (cell12705 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12705 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12705 ⟨14,by decide⟩).lower ∧ (cell12705 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12705 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12705 ⟨15,by decide⟩).lower ∧ (cell12705 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12705 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12705 ⟨16,by decide⟩).lower ∧ (cell12705 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12705 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12705 ⟨17,by decide⟩).lower ∧ (cell12705 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12705 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12705 ⟨18,by decide⟩).lower ∧ (cell12705 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12705 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12705 ⟨19,by decide⟩).lower ∧ (cell12705 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12705 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12705 ⟨20,by decide⟩).lower ∧ (cell12705 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12705 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12705 ⟨21,by decide⟩).lower ∧ (cell12705 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12705 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12705 ⟨22,by decide⟩).lower ∧ (cell12705 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12705 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12705 ⟨23,by decide⟩).lower ∧ (cell12705 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12705 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12705 ⟨24,by decide⟩).lower ∧ (cell12705 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12705 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12705 ⟨25,by decide⟩).lower ∧ (cell12705 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12705 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12705 ⟨26,by decide⟩).lower ∧ (cell12705 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12705 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12705 ⟨27,by decide⟩).lower ∧ (cell12705 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12705 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12705 ⟨28,by decide⟩).lower ∧ (cell12705 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12705 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12705 ⟨29,by decide⟩).lower ∧ (cell12705 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12705 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12705 ⟨30,by decide⟩).lower ∧ (cell12705 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12705 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12705 ⟨31,by decide⟩).lower ∧ (cell12705 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12705 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12705 ⟨32,by decide⟩).lower ∧ (cell12705 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12705 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12705 ⟨33,by decide⟩).lower ∧ (cell12705 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12705 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12705 ⟨34,by decide⟩).lower ∧ (cell12705 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12705 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12705 ⟨35,by decide⟩).lower ∧ (cell12705 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12705 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12705 ⟨36,by decide⟩).lower ∧ (cell12705 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12705 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12705 ⟨37,by decide⟩).lower ∧ (cell12705 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12705 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12705 ⟨38,by decide⟩).lower ∧ (cell12705 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12705 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12705 ⟨39,by decide⟩).lower ∧ (cell12705 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12705 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12705 ⟨40,by decide⟩).lower ∧ (cell12705 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12705 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12705 ⟨41,by decide⟩).lower ∧ (cell12705 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12705 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12705 ⟨42,by decide⟩).lower ∧ (cell12705 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12705 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12705 ⟨43,by decide⟩).lower ∧ (cell12705 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12705 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12705 ⟨44,by decide⟩).lower ∧ (cell12705 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12705 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12705 ⟨45,by decide⟩).lower ∧ (cell12705 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12705 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12705 ⟨46,by decide⟩).lower ∧ (cell12705 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12705 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12705 ⟨47,by decide⟩).lower ∧ (cell12705 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12705 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12705 ⟨48,by decide⟩).lower ∧ (cell12705 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12705 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12705 ⟨49,by decide⟩).lower ∧ (cell12705 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12705 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12705 ⟨50,by decide⟩).lower ∧ (cell12705 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12705 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12705 ⟨51,by decide⟩).lower ∧ (cell12705 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12705 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12705 ⟨52,by decide⟩).lower ∧ (cell12705 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12705 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12705 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12705 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12705,cell12705,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12705 i).lower ∧
    (cell12705 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12705 i).upper ≤ (0.532 : ℝ) ∧
    (cell12705 i).centre ≤ (0.1 : ℝ) ∧ (cell12705 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12705 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12705 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12705

/-! The local source numeric instances at 12705 have no network premises. -/
namespace BstLean.Part269.N12705
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12705)
open BstLean.Part268 (cell12705)

noncomputable def sourceNumerics12705 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12705 (cell12705 i)
      scalarRow12705.M scalarRow12705.H scalarRow12705.xi := by
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
    energy_allowance := scalarRow12705.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12705]
    centre_nonneg := (scalarRow12705.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12705])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12705
/-! Actual 12706 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12706
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12706 ≤ (1.035800690776 : ℝ) := by
  have hr : (112.720894247694 : ℝ) ≤ √(12706 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.720894247694 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12706 12706 (11 / 1000) ≤
    (0.008480122818 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12706) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.720894247694 : ℝ) ≤ √(12706 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12706)
  have hdiv : K / √(12706 : ℝ) ≤ K / 112.720894247694 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.720894247694 ≤ (0.008480122818 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12706.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12706 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12706 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12706 := gPlus_lower 12706
end BstLean.Part269.N12706

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12706
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035800690775 : ℝ) ≤ wn 12706 := by
  have hn : √(12706 : ℝ) ≤ 112.720894247695 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12706 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.720894247695 ≤ 2 / √(12706 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251759853 : ℝ) ≤ rhoBar 12706 BstLean.Part154.csC ∧
    rhoBar 12706 BstLean.Part154.csC ≤ 0.000251760243 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035800690775 : ℝ) / (1.295212 * 12706) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035800690776 : ℝ) / (1.29521 * 12706) := by gcongr
      _ ≤ (0.000251760243 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12706 BstLean.Part154.csC) ≤ 0.001007104356 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12706 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12706 BstLean.Part154.csC) (piBar (rhoBar 12706 BstLean.Part154.csC)) ≤ 0.000192296168 ∧
    cc1 (rhoBar 12706 BstLean.Part154.csC) (piBar (rhoBar 12706 BstLean.Part154.csC)) ≤ 0.000122359329 ∧
    cc2 (rhoBar 12706 BstLean.Part154.csC) ≤ 0.000071030529 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12706 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12706 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12706 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12706 BstLean.Part154.csC * nuR (rhoBar 12706 BstLean.Part154.csC)) ≤ 0.000503536332 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251760243 : ℝ) * 0.001007104356 := by gcongr
      _ ≤ (0.000503536332 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12706 BstLean.Part154.csC) * nuR (rhoBar 12706 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001007104356 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12706 BstLean.Part154.csC) * rhoBar 12706 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251760243 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251760243 / 2 + 0.399 * 0.001007104356 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192296168 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503536332 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122359329 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251760243 / 1.414213562 := by gcongr
      _ ≤ (0.000071030529 : ℝ) := by norm_num

end BstLean.Part269.N12706

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12706
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12706 BstLean.Part154.csC) (piBar (rhoBar 12706 BstLean.Part154.csC)) ≤ 1.59690E-7 := by
  have hr0 : 0 ≤ rhoBar 12706 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12706 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12706 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12706 BstLean.Part154.csC) (piBar (rhoBar 12706 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12706 BstLean.Part154.csC) (piBar (rhoBar 12706 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12706 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192296168 : ℝ) ^ 2 + 0.000122359329 ^ 2 + 3 * 0.000071030529 ^ 2 +
        2 * 0.797885 * 0.000192296168 * 0.000122359329 + 2 * 0.000192296168 * 0.000071030529 +
        4 * 0.797885 * 0.000122359329 * 0.000071030529 := by gcongr
    _ ≤ (1.59690E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12706 BstLean.Part154.csC Θ ≤ 0.002628012534 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12706 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12706 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12706 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12706 BstLean.Part154.csC) (piBar (rhoBar 12706 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12706 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035800690776 * 1.59690E-7 / (0.000251759853 : ℝ) := by gcongr
    _ ≤ 0.002628012534 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12706 BstLean.Part154.csC Θ ≤ 0.002915888270 + 0.000664054234 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12706 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12706 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12706 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035800690776 : ℝ) * ((2 * Θ * 0.000251760243 +
        (6863 / 10000) * 0.000251760243 * 12706 * 0.001007104356) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002915888270 + 0.000664054234 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12706 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12706 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12706 0.011 Θ ∧ gammaRatio 12706 0.011 Θ ≤ 0.000086548661 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12706 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035800690776 : ℝ) * 0.525 / ((1 - 0.011) * 12706) := by gcongr
      _ ≤ (0.000086548661 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12706 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12706 0.011 Θ) :=
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
    badAllowance 12706 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12706 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12706 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12706 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12706 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12706 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12706 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12706 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12706 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12706 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12706 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035800690776 : ℝ) * 12706 *
        (2.2721E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12706 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003531580747 + 0.003292066768 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12706

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12706
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12706 BstLean.Part154.csC) (piBar (rhoBar 12706 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12706 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12706 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12706 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12706 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12706 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12706 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12706 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12706 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12706 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12706 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12706 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12706 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12706 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12706 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052471784963 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12706) ≤ 0.010594642538 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12706 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035800690776)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010594642538 + 2 * 0.737676 / 12706) := by gcongr
    _ ≤ (0.052471784963 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12706 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12706

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12706
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503839501 : ℝ) ≤ plow 12706 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12706) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052766515801)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379706581) : eMP 12706 0.011 xi bn ≤ 0.001187807344 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12706 : ℝ) * (1 - 0.011))) ≤ 0.000587307785 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001379706581 / (12706 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587307785 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587307785 : ℝ) + 3.141593 * 0.052766515801 / (12706 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001187807344 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052766515801)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379706581) : PiBarMP 12706 12 0.011 xi bn ≤ 0.161212699584 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12706 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037144401746 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.099214983870 : ℝ) ≤ √((12706 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.720894247694 : ℝ) ≤ √(12706 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12706) ≤ 0.123600938014 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037144401746 + 0.052766515801 * 1.772454 / (2 * (112.099214983870 : ℝ))) * (1 + 0.001187807344) +
        8 / (12706 * 112.720894247694) + 0.123600938014 := by gcongr
    _ ≤ (0.161212699584 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052766515801)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379706581) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282181418634) :
    parallelOracle 12706 0.011 xi bn cd ≤ 0.162202859469 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12706 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12706 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503839501 : ℝ) ≤ plow 12706 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.720894247694 : ℝ) ≤ √(12706 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282181418634 : ℝ) / (2 * 0.560503839501 * 112.720894247694)) * 0.161212699584 +
        0.282181418634 ^ 2 / (2 * 0.560503839501 * 112.720894247694) := by gcongr
    _ ≤ (0.162202859469 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052766515801) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379706581)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282181418634) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12706 12706 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503839501 : ℝ) ≤ plow 12706 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.720894247694 : ℝ) ≤ √(12706 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12706 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12706 Θ 1.22 ≤ 0.011764460430 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.720894247694 := by gcongr <;> linarith
      _ ≤ (0.011764460430 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12706 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12706 12706 0.011 ≤ 0.008480122818 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12706 12706 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12706 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12706 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12706 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12706 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162202859469 + 0.011764460430 + (0.008480122818 : ℝ) *
        (1 + 2 * (0.282181418634 + 0.011764460430) / (0.560503839501 * 112.720894247694))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12706]

end BstLean.Part269.N12706

/-! The original eight local profiles supply actual 12706 moment certificates. -/
namespace BstLean.Part269.N12706
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12706 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12706 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12706 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052766515801 ∧
    0 ≤ bN 12706 BstLean.Part154.csC (groupTheta g) ∧ bN 12706 BstLean.Part154.csC (groupTheta g) ≤ 0.001379706581 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12706 12706 0.011
      (momentAllowance 12706 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12706 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12706 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12706 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12706 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12706 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229709633671 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12706 0.011
      (momentAllowance 12706 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12706 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12706
/-! The actual computed-centre upper energy formula at 12706. -/
namespace BstLean.Part269.N12706
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12706

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12706
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12706)
open BstLean.Part268 (cell12706)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085472777915
  | 2 => 0.086415206507
  | 3 => 0.087355728019
  | 4 => 0.088295749746
  | 5 => 0.089236974243
  | 6 => 0.090181443230
  | 7 => 0.091131585626
  | 8 => 0.092090269777
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12706 12706 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12706 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003533030491 + 0.003293667169 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S14.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12706

/-! Actual upper energy certificates on all 43 source endpoints at 12706. -/
namespace BstLean.Part269.N12706
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12706)
open BstLean.Part268 (cell12706)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12706 (gMinus 12706) (1 - (cell12706 i).lower) ≤ 1 ∧
    energyUpper 12706 (gMinus 12706) (BstLean.Part211.gPlus 12706)
      (finiteEnergy 12706 12706 0.011) (1 - (cell12706 i).lower) ≤
      (cell12706 i).energy := by
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨10,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨11,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨12,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨13,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨14,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨15,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨16,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨17,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨18,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨19,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨20,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨21,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨22,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨23,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨24,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨25,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨26,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨27,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨28,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨29,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨30,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨31,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨32,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨33,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨34,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨35,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨36,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨37,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨38,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨39,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨40,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨41,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨42,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨43,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨44,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨45,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨46,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨47,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨48,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨49,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨50,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨51,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12706) (by norm_num)
        (q := 1 - (cell12706 ⟨52,by decide⟩).lower)
        (by norm_num [cell12706]) (by norm_num [cell12706])
      exact ⟨E.1,E.2.trans (by norm_num [cell12706])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12706

/-! Source-cell containment and simple scalar guards at 12706. -/
namespace BstLean.Part269.N12706
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12706)
open BstLean.Part268 (cell12706)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12706 ⟨10,by decide⟩).lower ∧ (cell12706 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12706 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12706 ⟨11,by decide⟩).lower ∧ (cell12706 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12706 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12706 ⟨12,by decide⟩).lower ∧ (cell12706 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12706 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12706 ⟨13,by decide⟩).lower ∧ (cell12706 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12706 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12706 ⟨14,by decide⟩).lower ∧ (cell12706 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12706 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12706 ⟨15,by decide⟩).lower ∧ (cell12706 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12706 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12706 ⟨16,by decide⟩).lower ∧ (cell12706 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12706 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12706 ⟨17,by decide⟩).lower ∧ (cell12706 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12706 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12706 ⟨18,by decide⟩).lower ∧ (cell12706 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12706 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12706 ⟨19,by decide⟩).lower ∧ (cell12706 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12706 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12706 ⟨20,by decide⟩).lower ∧ (cell12706 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12706 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12706 ⟨21,by decide⟩).lower ∧ (cell12706 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12706 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12706 ⟨22,by decide⟩).lower ∧ (cell12706 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12706 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12706 ⟨23,by decide⟩).lower ∧ (cell12706 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12706 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12706 ⟨24,by decide⟩).lower ∧ (cell12706 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12706 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12706 ⟨25,by decide⟩).lower ∧ (cell12706 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12706 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12706 ⟨26,by decide⟩).lower ∧ (cell12706 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12706 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12706 ⟨27,by decide⟩).lower ∧ (cell12706 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12706 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12706 ⟨28,by decide⟩).lower ∧ (cell12706 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12706 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12706 ⟨29,by decide⟩).lower ∧ (cell12706 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12706 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12706 ⟨30,by decide⟩).lower ∧ (cell12706 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12706 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12706 ⟨31,by decide⟩).lower ∧ (cell12706 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12706 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12706 ⟨32,by decide⟩).lower ∧ (cell12706 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12706 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12706 ⟨33,by decide⟩).lower ∧ (cell12706 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12706 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12706 ⟨34,by decide⟩).lower ∧ (cell12706 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12706 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12706 ⟨35,by decide⟩).lower ∧ (cell12706 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12706 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12706 ⟨36,by decide⟩).lower ∧ (cell12706 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12706 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12706 ⟨37,by decide⟩).lower ∧ (cell12706 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12706 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12706 ⟨38,by decide⟩).lower ∧ (cell12706 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12706 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12706 ⟨39,by decide⟩).lower ∧ (cell12706 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12706 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12706 ⟨40,by decide⟩).lower ∧ (cell12706 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12706 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12706 ⟨41,by decide⟩).lower ∧ (cell12706 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12706 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12706 ⟨42,by decide⟩).lower ∧ (cell12706 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12706 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12706 ⟨43,by decide⟩).lower ∧ (cell12706 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12706 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12706 ⟨44,by decide⟩).lower ∧ (cell12706 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12706 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12706 ⟨45,by decide⟩).lower ∧ (cell12706 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12706 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12706 ⟨46,by decide⟩).lower ∧ (cell12706 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12706 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12706 ⟨47,by decide⟩).lower ∧ (cell12706 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12706 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12706 ⟨48,by decide⟩).lower ∧ (cell12706 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12706 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12706 ⟨49,by decide⟩).lower ∧ (cell12706 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12706 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12706 ⟨50,by decide⟩).lower ∧ (cell12706 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12706 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12706 ⟨51,by decide⟩).lower ∧ (cell12706 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12706 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12706 ⟨52,by decide⟩).lower ∧ (cell12706 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12706 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12706 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12706 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12706,cell12706,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12706 i).lower ∧
    (cell12706 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12706 i).upper ≤ (0.532 : ℝ) ∧
    (cell12706 i).centre ≤ (0.1 : ℝ) ∧ (cell12706 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12706 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12706 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12706

/-! The local source numeric instances at 12706 have no network premises. -/
namespace BstLean.Part269.N12706
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12706)
open BstLean.Part268 (cell12706)

noncomputable def sourceNumerics12706 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12706 (cell12706 i)
      scalarRow12706.M scalarRow12706.H scalarRow12706.xi := by
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
    energy_allowance := scalarRow12706.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12706]
    centre_nonneg := (scalarRow12706.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12706])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12706
/-! Actual 12707 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12707
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12707 ≤ (1.035799269661 : ℝ) := by
  have hr : (112.725329895281 : ℝ) ≤ √(12707 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.725329895281 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12707 12707 (11 / 1000) ≤
    (0.008479789130 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12707) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.725329895281 : ℝ) ≤ √(12707 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12707)
  have hdiv : K / √(12707 : ℝ) ≤ K / 112.725329895281 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.725329895281 ≤ (0.008479789130 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12707.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12707 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12707 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12707 := gPlus_lower 12707
end BstLean.Part269.N12707

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12707
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035799269660 : ℝ) ≤ wn 12707 := by
  have hn : √(12707 : ℝ) ≤ 112.725329895282 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12707 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.725329895282 ≤ 2 / √(12707 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251739695 : ℝ) ≤ rhoBar 12707 BstLean.Part154.csC ∧
    rhoBar 12707 BstLean.Part154.csC ≤ 0.000251740085 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035799269660 : ℝ) / (1.295212 * 12707) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035799269661 : ℝ) / (1.29521 * 12707) := by gcongr
      _ ≤ (0.000251740085 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12707 BstLean.Part154.csC) ≤ 0.001007023714 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12707 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12707 BstLean.Part154.csC) (piBar (rhoBar 12707 BstLean.Part154.csC)) ≤ 0.000192280770 ∧
    cc1 (rhoBar 12707 BstLean.Part154.csC) (piBar (rhoBar 12707 BstLean.Part154.csC)) ≤ 0.000122349532 ∧
    cc2 (rhoBar 12707 BstLean.Part154.csC) ≤ 0.000071024842 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12707 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12707 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12707 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12707 BstLean.Part154.csC * nuR (rhoBar 12707 BstLean.Part154.csC)) ≤ 0.000503496014 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251740085 : ℝ) * 0.001007023714 := by gcongr
      _ ≤ (0.000503496014 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12707 BstLean.Part154.csC) * nuR (rhoBar 12707 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001007023714 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12707 BstLean.Part154.csC) * rhoBar 12707 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251740085 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251740085 / 2 + 0.399 * 0.001007023714 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192280770 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503496014 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122349532 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251740085 / 1.414213562 := by gcongr
      _ ≤ (0.000071024842 : ℝ) := by norm_num

end BstLean.Part269.N12707

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12707
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12707 BstLean.Part154.csC) (piBar (rhoBar 12707 BstLean.Part154.csC)) ≤ 1.59664E-7 := by
  have hr0 : 0 ≤ rhoBar 12707 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12707 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12707 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12707 BstLean.Part154.csC) (piBar (rhoBar 12707 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12707 BstLean.Part154.csC) (piBar (rhoBar 12707 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12707 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192280770 : ℝ) ^ 2 + 0.000122349532 ^ 2 + 3 * 0.000071024842 ^ 2 +
        2 * 0.797885 * 0.000192280770 * 0.000122349532 + 2 * 0.000192280770 * 0.000071024842 +
        4 * 0.797885 * 0.000122349532 * 0.000071024842 := by gcongr
    _ ≤ (1.59664E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12707 BstLean.Part154.csC Θ ≤ 0.002627791451 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12707 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12707 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12707 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12707 BstLean.Part154.csC) (piBar (rhoBar 12707 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12707 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035799269661 * 1.59664E-7 / (0.000251739695 : ℝ) := by gcongr
    _ ≤ 0.002627791451 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12707 BstLean.Part154.csC Θ ≤ 0.002915646786 + 0.000664000154 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12707 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12707 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12707 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035799269661 : ℝ) * ((2 * Θ * 0.000251740085 +
        (6863 / 10000) * 0.000251740085 * 12707 * 0.001007023714) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002915646786 + 0.000664000154 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12707 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12707 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12707 0.011 Θ ∧ gammaRatio 12707 0.011 Θ ≤ 0.000086541732 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12707 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035799269661 : ℝ) * 0.525 / ((1 - 0.011) * 12707) := by gcongr
      _ ≤ (0.000086541732 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12707 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12707 0.011 Θ) :=
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
    badAllowance 12707 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12707 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12707 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12707 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12707 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12707 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12707 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12707 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12707 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12707 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12707 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035799269661 : ℝ) * 12707 *
        (2.2721E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12707 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003531339263 + 0.003291791605 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12707

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12707
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12707 BstLean.Part154.csC) (piBar (rhoBar 12707 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12707 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12707 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12707 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12707 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12707 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12707 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12707 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12707 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12707 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12707 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12707 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12707 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12707 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12707 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052469697861 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12707) ≤ 0.010594225648 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12707 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035799269661)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010594225648 + 2 * 0.737676 / 12707) := by gcongr
    _ ≤ (0.052469697861 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12707 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12707

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12707
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503884677 : ℝ) ≤ plow 12707 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12707) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052766129856)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379590512) : eMP 12707 0.011 xi bn ≤ 0.001187710582 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12707 : ℝ) * (1 - 0.011))) ≤ 0.000587259971 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001379590512 / (12707 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587259971 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587259971 : ℝ) + 3.141593 * 0.052766129856 / (12707 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001187710582 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052766129856)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379590512) : PiBarMP 12707 12 0.011 xi bn ≤ 0.161206247915 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12707 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037142839310 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.103626167934 : ℝ) ≤ √((12707 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.725329895281 : ℝ) ≤ √(12707 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12707) ≤ 0.123596074420 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037142839310 + 0.052766129856 * 1.772454 / (2 * (112.103626167934 : ℝ))) * (1 + 0.001187710582) +
        8 / (12707 * 112.725329895281) + 0.123596074420 := by gcongr
    _ ≤ (0.161206247915 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052766129856)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379590512) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282178491459) :
    parallelOracle 12707 0.011 xi bn cd ≤ 0.162196337544 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12707 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12707 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503884677 : ℝ) ≤ plow 12707 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.725329895281 : ℝ) ≤ √(12707 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282178491459 : ℝ) / (2 * 0.560503884677 * 112.725329895281)) * 0.161206247915 +
        0.282178491459 ^ 2 / (2 * 0.560503884677 * 112.725329895281) := by gcongr
    _ ≤ (0.162196337544 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052766129856) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379590512)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282178491459) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12707 12707 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503884677 : ℝ) ≤ plow 12707 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.725329895281 : ℝ) ≤ √(12707 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12707 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12707 Θ 1.22 ≤ 0.011763997509 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.725329895281 := by gcongr <;> linarith
      _ ≤ (0.011763997509 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12707 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12707 12707 0.011 ≤ 0.008479789130 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12707 12707 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12707 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12707 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12707 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12707 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162196337544 + 0.011763997509 + (0.008479789130 : ℝ) *
        (1 + 2 * (0.282178491459 + 0.011763997509) / (0.560503884677 * 112.725329895281))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12707]

end BstLean.Part269.N12707

/-! The original eight local profiles supply actual 12707 moment certificates. -/
namespace BstLean.Part269.N12707
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12707 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12707 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12707 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052766129856 ∧
    0 ≤ bN 12707 BstLean.Part154.csC (groupTheta g) ∧ bN 12707 BstLean.Part154.csC (groupTheta g) ≤ 0.001379590512 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12707 12707 0.011
      (momentAllowance 12707 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12707 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12707 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12707 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12707 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12707 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229708793598 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12707 0.011
      (momentAllowance 12707 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12707 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12707
/-! The actual computed-centre upper energy formula at 12707. -/
namespace BstLean.Part269.N12707
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12707

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12707
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12707)
open BstLean.Part268 (cell12707)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085469868643
  | 2 => 0.086412243945
  | 3 => 0.087352704417
  | 4 => 0.088292655570
  | 5 => 0.089233797855
  | 6 => 0.090178170533
  | 7 => 0.091128199672
  | 8 => 0.092086750321
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12707 12707 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12707 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003533030491 + 0.003293667169 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S14.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12707

/-! Actual upper energy certificates on all 43 source endpoints at 12707. -/
namespace BstLean.Part269.N12707
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12707)
open BstLean.Part268 (cell12707)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12707 (gMinus 12707) (1 - (cell12707 i).lower) ≤ 1 ∧
    energyUpper 12707 (gMinus 12707) (BstLean.Part211.gPlus 12707)
      (finiteEnergy 12707 12707 0.011) (1 - (cell12707 i).lower) ≤
      (cell12707 i).energy := by
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨10,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨11,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨12,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨13,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨14,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨15,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨16,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨17,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨18,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨19,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨20,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨21,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨22,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨23,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨24,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨25,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨26,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨27,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨28,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨29,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨30,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨31,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨32,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨33,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨34,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨35,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨36,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨37,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨38,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨39,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨40,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨41,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨42,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨43,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨44,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨45,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨46,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨47,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨48,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨49,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨50,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨51,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12707) (by norm_num)
        (q := 1 - (cell12707 ⟨52,by decide⟩).lower)
        (by norm_num [cell12707]) (by norm_num [cell12707])
      exact ⟨E.1,E.2.trans (by norm_num [cell12707])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12707

/-! Source-cell containment and simple scalar guards at 12707. -/
namespace BstLean.Part269.N12707
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12707)
open BstLean.Part268 (cell12707)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12707 ⟨10,by decide⟩).lower ∧ (cell12707 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12707 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12707 ⟨11,by decide⟩).lower ∧ (cell12707 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12707 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12707 ⟨12,by decide⟩).lower ∧ (cell12707 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12707 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12707 ⟨13,by decide⟩).lower ∧ (cell12707 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12707 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12707 ⟨14,by decide⟩).lower ∧ (cell12707 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12707 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12707 ⟨15,by decide⟩).lower ∧ (cell12707 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12707 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12707 ⟨16,by decide⟩).lower ∧ (cell12707 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12707 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12707 ⟨17,by decide⟩).lower ∧ (cell12707 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12707 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12707 ⟨18,by decide⟩).lower ∧ (cell12707 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12707 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12707 ⟨19,by decide⟩).lower ∧ (cell12707 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12707 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12707 ⟨20,by decide⟩).lower ∧ (cell12707 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12707 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12707 ⟨21,by decide⟩).lower ∧ (cell12707 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12707 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12707 ⟨22,by decide⟩).lower ∧ (cell12707 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12707 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12707 ⟨23,by decide⟩).lower ∧ (cell12707 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12707 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12707 ⟨24,by decide⟩).lower ∧ (cell12707 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12707 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12707 ⟨25,by decide⟩).lower ∧ (cell12707 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12707 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12707 ⟨26,by decide⟩).lower ∧ (cell12707 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12707 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12707 ⟨27,by decide⟩).lower ∧ (cell12707 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12707 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12707 ⟨28,by decide⟩).lower ∧ (cell12707 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12707 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12707 ⟨29,by decide⟩).lower ∧ (cell12707 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12707 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12707 ⟨30,by decide⟩).lower ∧ (cell12707 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12707 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12707 ⟨31,by decide⟩).lower ∧ (cell12707 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12707 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12707 ⟨32,by decide⟩).lower ∧ (cell12707 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12707 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12707 ⟨33,by decide⟩).lower ∧ (cell12707 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12707 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12707 ⟨34,by decide⟩).lower ∧ (cell12707 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12707 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12707 ⟨35,by decide⟩).lower ∧ (cell12707 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12707 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12707 ⟨36,by decide⟩).lower ∧ (cell12707 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12707 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12707 ⟨37,by decide⟩).lower ∧ (cell12707 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12707 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12707 ⟨38,by decide⟩).lower ∧ (cell12707 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12707 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12707 ⟨39,by decide⟩).lower ∧ (cell12707 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12707 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12707 ⟨40,by decide⟩).lower ∧ (cell12707 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12707 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12707 ⟨41,by decide⟩).lower ∧ (cell12707 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12707 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12707 ⟨42,by decide⟩).lower ∧ (cell12707 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12707 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12707 ⟨43,by decide⟩).lower ∧ (cell12707 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12707 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12707 ⟨44,by decide⟩).lower ∧ (cell12707 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12707 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12707 ⟨45,by decide⟩).lower ∧ (cell12707 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12707 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12707 ⟨46,by decide⟩).lower ∧ (cell12707 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12707 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12707 ⟨47,by decide⟩).lower ∧ (cell12707 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12707 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12707 ⟨48,by decide⟩).lower ∧ (cell12707 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12707 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12707 ⟨49,by decide⟩).lower ∧ (cell12707 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12707 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12707 ⟨50,by decide⟩).lower ∧ (cell12707 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12707 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12707 ⟨51,by decide⟩).lower ∧ (cell12707 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12707 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12707 ⟨52,by decide⟩).lower ∧ (cell12707 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12707 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12707 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12707 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12707,cell12707,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12707 i).lower ∧
    (cell12707 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12707 i).upper ≤ (0.532 : ℝ) ∧
    (cell12707 i).centre ≤ (0.1 : ℝ) ∧ (cell12707 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12707 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12707 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12707

/-! The local source numeric instances at 12707 have no network premises. -/
namespace BstLean.Part269.N12707
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12707)
open BstLean.Part268 (cell12707)

noncomputable def sourceNumerics12707 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12707 (cell12707 i)
      scalarRow12707.M scalarRow12707.H scalarRow12707.xi := by
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
    energy_allowance := scalarRow12707.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12707]
    centre_nonneg := (scalarRow12707.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12707])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12707
/-! Actual 12708 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12708
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12708 ≤ (1.035797848716 : ℝ) := by
  have hr : (112.729765368335 : ℝ) ≤ √(12708 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.729765368335 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12708 12708 (11 / 1000) ≤
    (0.008479455481 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12708) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.729765368335 : ℝ) ≤ √(12708 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12708)
  have hdiv : K / √(12708 : ℝ) ≤ K / 112.729765368335 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.729765368335 ≤ (0.008479455481 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12708.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12708 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12708 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12708 := gPlus_lower 12708
end BstLean.Part269.N12708

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12708
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035797848715 : ℝ) ≤ wn 12708 := by
  have hn : √(12708 : ℝ) ≤ 112.729765368336 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12708 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.729765368336 ≤ 2 / √(12708 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251719540 : ℝ) ≤ rhoBar 12708 BstLean.Part154.csC ∧
    rhoBar 12708 BstLean.Part154.csC ≤ 0.000251719930 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035797848715 : ℝ) / (1.295212 * 12708) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035797848716 : ℝ) / (1.29521 * 12708) := by gcongr
      _ ≤ (0.000251719930 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12708 BstLean.Part154.csC) ≤ 0.001006943083 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12708 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12708 BstLean.Part154.csC) (piBar (rhoBar 12708 BstLean.Part154.csC)) ≤ 0.000192265375 ∧
    cc1 (rhoBar 12708 BstLean.Part154.csC) (piBar (rhoBar 12708 BstLean.Part154.csC)) ≤ 0.000122339736 ∧
    cc2 (rhoBar 12708 BstLean.Part154.csC) ≤ 0.000071019155 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12708 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12708 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12708 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12708 BstLean.Part154.csC * nuR (rhoBar 12708 BstLean.Part154.csC)) ≤ 0.000503455701 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251719930 : ℝ) * 0.001006943083 := by gcongr
      _ ≤ (0.000503455701 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12708 BstLean.Part154.csC) * nuR (rhoBar 12708 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001006943083 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12708 BstLean.Part154.csC) * rhoBar 12708 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251719930 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251719930 / 2 + 0.399 * 0.001006943083 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192265375 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503455701 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122339736 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251719930 / 1.414213562 := by gcongr
      _ ≤ (0.000071019155 : ℝ) := by norm_num

end BstLean.Part269.N12708

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12708
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12708 BstLean.Part154.csC) (piBar (rhoBar 12708 BstLean.Part154.csC)) ≤ 1.59638E-7 := by
  have hr0 : 0 ≤ rhoBar 12708 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12708 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12708 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12708 BstLean.Part154.csC) (piBar (rhoBar 12708 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12708 BstLean.Part154.csC) (piBar (rhoBar 12708 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12708 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192265375 : ℝ) ^ 2 + 0.000122339736 ^ 2 + 3 * 0.000071019155 ^ 2 +
        2 * 0.797885 * 0.000192265375 * 0.000122339736 + 2 * 0.000192265375 * 0.000071019155 +
        4 * 0.797885 * 0.000122339736 * 0.000071019155 := by gcongr
    _ ≤ (1.59638E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12708 BstLean.Part154.csC Θ ≤ 0.002627570303 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12708 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12708 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12708 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12708 BstLean.Part154.csC) (piBar (rhoBar 12708 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12708 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035797848716 * 1.59638E-7 / (0.000251719540 : ℝ) := by gcongr
    _ ≤ 0.002627570303 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12708 BstLean.Part154.csC Θ ≤ 0.002915405334 + 0.000663946081 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12708 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12708 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12708 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035797848716 : ℝ) * ((2 * Θ * 0.000251719930 +
        (6863 / 10000) * 0.000251719930 * 12708 * 0.001006943083) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002915405334 + 0.000663946081 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12708 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12708 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12708 0.011 Θ ∧ gammaRatio 12708 0.011 Θ ≤ 0.000086534803 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12708 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035797848716 : ℝ) * 0.525 / ((1 - 0.011) * 12708) := by gcongr
      _ ≤ (0.000086534803 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12708 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12708 0.011 Θ) :=
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
    badAllowance 12708 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12708 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12708 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12708 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12708 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12708 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12708 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12708 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12708 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12708 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12708 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035797848716 : ℝ) * 12708 *
        (2.2721E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12708 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003531097811 + 0.003291516384 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12708

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12708
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12708 BstLean.Part154.csC) (piBar (rhoBar 12708 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12708 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12708 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12708 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12708 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12708 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12708 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12708 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12708 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12708 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12708 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12708 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12708 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12708 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12708 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052467611001 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12708) ≤ 0.010593808806 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12708 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035797848716)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010593808806 + 2 * 0.737676 / 12708) := by gcongr
    _ ≤ (0.052467611001 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12708 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12708

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12708
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503929847 : ℝ) ≤ plow 12708 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12708) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052765743913)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379474410) : eMP 12708 0.011 xi bn ≤ 0.001187613813 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12708 : ℝ) * (1 - 0.011))) ≤ 0.000587212154 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001379474410 / (12708 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587212154 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587212154 : ℝ) + 3.141593 * 0.052765743913 / (12708 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001187613813 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052765743913)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379474410) : PiBarMP 12708 12 0.011 xi bn ≤ 0.161199796314 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12708 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037141276365 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.108037178428 : ℝ) ≤ √((12708 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.729765368335 : ℝ) ≤ √(12708 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12708) ≤ 0.123591211401 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037141276365 + 0.052765743913 * 1.772454 / (2 * (112.108037178428 : ℝ))) * (1 + 0.001187613813) +
        8 / (12708 * 112.729765368335) + 0.123591211401 := by gcongr
    _ ≤ (0.161199796314 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052765743913)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379474410) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282175564527) :
    parallelOracle 12708 0.011 xi bn cd ≤ 0.162189815696 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12708 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12708 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503929847 : ℝ) ≤ plow 12708 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.729765368335 : ℝ) ≤ √(12708 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282175564527 : ℝ) / (2 * 0.560503929847 * 112.729765368335)) * 0.161199796314 +
        0.282175564527 ^ 2 / (2 * 0.560503929847 * 112.729765368335) := by gcongr
    _ ≤ (0.162189815696 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052765743913) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379474410)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282175564527) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12708 12708 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503929847 : ℝ) ≤ plow 12708 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.729765368335 : ℝ) ≤ √(12708 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12708 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12708 Θ 1.22 ≤ 0.011763534642 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.729765368335 := by gcongr <;> linarith
      _ ≤ (0.011763534642 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12708 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12708 12708 0.011 ≤ 0.008479455481 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12708 12708 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12708 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12708 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12708 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12708 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162189815696 + 0.011763534642 + (0.008479455481 : ℝ) *
        (1 + 2 * (0.282175564527 + 0.011763534642) / (0.560503929847 * 112.729765368335))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12708]

end BstLean.Part269.N12708

/-! The original eight local profiles supply actual 12708 moment certificates. -/
namespace BstLean.Part269.N12708
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12708 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12708 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12708 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052765743913 ∧
    0 ≤ bN 12708 BstLean.Part154.csC (groupTheta g) ∧ bN 12708 BstLean.Part154.csC (groupTheta g) ≤ 0.001379474410 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12708 12708 0.011
      (momentAllowance 12708 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12708 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12708 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12708 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12708 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12708 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229707953526 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12708 0.011
      (momentAllowance 12708 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12708 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12708
/-! The actual computed-centre upper energy formula at 12708. -/
namespace BstLean.Part269.N12708
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12708

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12708
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12708)
open BstLean.Part268 (cell12708)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085466960447
  | 2 => 0.086409282502
  | 3 => 0.087349681990
  | 4 => 0.088289562635
  | 5 => 0.089230622790
  | 6 => 0.090174899260
  | 7 => 0.091124815261
  | 8 => 0.092083232553
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12708 12708 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12708 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003533030491 + 0.003293667169 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S14.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12708

/-! Actual upper energy certificates on all 43 source endpoints at 12708. -/
namespace BstLean.Part269.N12708
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12708)
open BstLean.Part268 (cell12708)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12708 (gMinus 12708) (1 - (cell12708 i).lower) ≤ 1 ∧
    energyUpper 12708 (gMinus 12708) (BstLean.Part211.gPlus 12708)
      (finiteEnergy 12708 12708 0.011) (1 - (cell12708 i).lower) ≤
      (cell12708 i).energy := by
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨10,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨11,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨12,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨13,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨14,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨15,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨16,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨17,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨18,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨19,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨20,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨21,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨22,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨23,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨24,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨25,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨26,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨27,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨28,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨29,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨30,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨31,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨32,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨33,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨34,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨35,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨36,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨37,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨38,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨39,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨40,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨41,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨42,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨43,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨44,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨45,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨46,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨47,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨48,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨49,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨50,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨51,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12708) (by norm_num)
        (q := 1 - (cell12708 ⟨52,by decide⟩).lower)
        (by norm_num [cell12708]) (by norm_num [cell12708])
      exact ⟨E.1,E.2.trans (by norm_num [cell12708])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12708

/-! Source-cell containment and simple scalar guards at 12708. -/
namespace BstLean.Part269.N12708
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12708)
open BstLean.Part268 (cell12708)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12708 ⟨10,by decide⟩).lower ∧ (cell12708 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12708 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12708 ⟨11,by decide⟩).lower ∧ (cell12708 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12708 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12708 ⟨12,by decide⟩).lower ∧ (cell12708 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12708 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12708 ⟨13,by decide⟩).lower ∧ (cell12708 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12708 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12708 ⟨14,by decide⟩).lower ∧ (cell12708 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12708 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12708 ⟨15,by decide⟩).lower ∧ (cell12708 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12708 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12708 ⟨16,by decide⟩).lower ∧ (cell12708 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12708 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12708 ⟨17,by decide⟩).lower ∧ (cell12708 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12708 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12708 ⟨18,by decide⟩).lower ∧ (cell12708 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12708 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12708 ⟨19,by decide⟩).lower ∧ (cell12708 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12708 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12708 ⟨20,by decide⟩).lower ∧ (cell12708 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12708 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12708 ⟨21,by decide⟩).lower ∧ (cell12708 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12708 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12708 ⟨22,by decide⟩).lower ∧ (cell12708 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12708 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12708 ⟨23,by decide⟩).lower ∧ (cell12708 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12708 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12708 ⟨24,by decide⟩).lower ∧ (cell12708 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12708 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12708 ⟨25,by decide⟩).lower ∧ (cell12708 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12708 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12708 ⟨26,by decide⟩).lower ∧ (cell12708 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12708 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12708 ⟨27,by decide⟩).lower ∧ (cell12708 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12708 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12708 ⟨28,by decide⟩).lower ∧ (cell12708 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12708 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12708 ⟨29,by decide⟩).lower ∧ (cell12708 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12708 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12708 ⟨30,by decide⟩).lower ∧ (cell12708 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12708 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12708 ⟨31,by decide⟩).lower ∧ (cell12708 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12708 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12708 ⟨32,by decide⟩).lower ∧ (cell12708 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12708 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12708 ⟨33,by decide⟩).lower ∧ (cell12708 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12708 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12708 ⟨34,by decide⟩).lower ∧ (cell12708 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12708 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12708 ⟨35,by decide⟩).lower ∧ (cell12708 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12708 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12708 ⟨36,by decide⟩).lower ∧ (cell12708 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12708 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12708 ⟨37,by decide⟩).lower ∧ (cell12708 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12708 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12708 ⟨38,by decide⟩).lower ∧ (cell12708 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12708 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12708 ⟨39,by decide⟩).lower ∧ (cell12708 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12708 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12708 ⟨40,by decide⟩).lower ∧ (cell12708 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12708 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12708 ⟨41,by decide⟩).lower ∧ (cell12708 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12708 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12708 ⟨42,by decide⟩).lower ∧ (cell12708 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12708 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12708 ⟨43,by decide⟩).lower ∧ (cell12708 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12708 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12708 ⟨44,by decide⟩).lower ∧ (cell12708 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12708 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12708 ⟨45,by decide⟩).lower ∧ (cell12708 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12708 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12708 ⟨46,by decide⟩).lower ∧ (cell12708 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12708 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12708 ⟨47,by decide⟩).lower ∧ (cell12708 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12708 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12708 ⟨48,by decide⟩).lower ∧ (cell12708 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12708 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12708 ⟨49,by decide⟩).lower ∧ (cell12708 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12708 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12708 ⟨50,by decide⟩).lower ∧ (cell12708 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12708 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12708 ⟨51,by decide⟩).lower ∧ (cell12708 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12708 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12708 ⟨52,by decide⟩).lower ∧ (cell12708 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12708 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12708 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12708 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12708,cell12708,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12708 i).lower ∧
    (cell12708 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12708 i).upper ≤ (0.532 : ℝ) ∧
    (cell12708 i).centre ≤ (0.1 : ℝ) ∧ (cell12708 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12708 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12708 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12708

/-! The local source numeric instances at 12708 have no network premises. -/
namespace BstLean.Part269.N12708
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12708)
open BstLean.Part268 (cell12708)

noncomputable def sourceNumerics12708 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12708 (cell12708 i)
      scalarRow12708.M scalarRow12708.H scalarRow12708.xi := by
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
    energy_allowance := scalarRow12708.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12708]
    centre_nonneg := (scalarRow12708.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12708])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12708
/-! Actual 12709 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12709
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12709 ≤ (1.035796427939 : ℝ) := by
  have hr : (112.734200666878 : ℝ) ≤ √(12709 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.734200666878 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12709 12709 (11 / 1000) ≤
    (0.008479121871 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12709) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.734200666878 : ℝ) ≤ √(12709 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12709)
  have hdiv : K / √(12709 : ℝ) ≤ K / 112.734200666878 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.734200666878 ≤ (0.008479121871 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12709.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12709 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12709 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12709 := gPlus_lower 12709
end BstLean.Part269.N12709

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12709
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035796427938 : ℝ) ≤ wn 12709 := by
  have hn : √(12709 : ℝ) ≤ 112.734200666879 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12709 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.734200666879 ≤ 2 / √(12709 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251699388 : ℝ) ≤ rhoBar 12709 BstLean.Part154.csC ∧
    rhoBar 12709 BstLean.Part154.csC ≤ 0.000251699778 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035796427938 : ℝ) / (1.295212 * 12709) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035796427939 : ℝ) / (1.29521 * 12709) := by gcongr
      _ ≤ (0.000251699778 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12709 BstLean.Part154.csC) ≤ 0.001006862465 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12709 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12709 BstLean.Part154.csC) (piBar (rhoBar 12709 BstLean.Part154.csC)) ≤ 0.000192249982 ∧
    cc1 (rhoBar 12709 BstLean.Part154.csC) (piBar (rhoBar 12709 BstLean.Part154.csC)) ≤ 0.000122329941 ∧
    cc2 (rhoBar 12709 BstLean.Part154.csC) ≤ 0.000071013470 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12709 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12709 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12709 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12709 BstLean.Part154.csC * nuR (rhoBar 12709 BstLean.Part154.csC)) ≤ 0.000503415395 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251699778 : ℝ) * 0.001006862465 := by gcongr
      _ ≤ (0.000503415395 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12709 BstLean.Part154.csC) * nuR (rhoBar 12709 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001006862465 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12709 BstLean.Part154.csC) * rhoBar 12709 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251699778 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251699778 / 2 + 0.399 * 0.001006862465 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192249982 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503415395 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122329941 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251699778 / 1.414213562 := by gcongr
      _ ≤ (0.000071013470 : ℝ) := by norm_num

end BstLean.Part269.N12709

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12709
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12709 BstLean.Part154.csC) (piBar (rhoBar 12709 BstLean.Part154.csC)) ≤ 1.59613E-7 := by
  have hr0 : 0 ≤ rhoBar 12709 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12709 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12709 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12709 BstLean.Part154.csC) (piBar (rhoBar 12709 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12709 BstLean.Part154.csC) (piBar (rhoBar 12709 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12709 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192249982 : ℝ) ^ 2 + 0.000122329941 ^ 2 + 3 * 0.000071013470 ^ 2 +
        2 * 0.797885 * 0.000192249982 * 0.000122329941 + 2 * 0.000192249982 * 0.000071013470 +
        4 * 0.797885 * 0.000122329941 * 0.000071013470 := by gcongr
    _ ≤ (1.59613E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12709 BstLean.Part154.csC Θ ≤ 0.002627365551 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12709 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12709 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12709 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12709 BstLean.Part154.csC) (piBar (rhoBar 12709 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12709 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035796427939 * 1.59613E-7 / (0.000251699388 : ℝ) := by gcongr
    _ ≤ 0.002627365551 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12709 BstLean.Part154.csC Θ ≤ 0.002915163920 + 0.000663892017 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12709 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12709 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12709 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035796427939 : ℝ) * ((2 * Θ * 0.000251699778 +
        (6863 / 10000) * 0.000251699778 * 12709 * 0.001006862465) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002915163920 + 0.000663892017 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12709 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12709 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12709 0.011 Θ ∧ gammaRatio 12709 0.011 Θ ≤ 0.000086527875 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12709 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035796427939 : ℝ) * 0.525 / ((1 - 0.011) * 12709) := by gcongr
      _ ≤ (0.000086527875 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12709 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12709 0.011 Θ) :=
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
    badAllowance 12709 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12709 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12709 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12709 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12709 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12709 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12709 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12709 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12709 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12709 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12709 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035796427939 : ℝ) * 12709 *
        (2.2721E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12709 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003530856397 + 0.003291257568 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12709

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12709
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12709 BstLean.Part154.csC) (piBar (rhoBar 12709 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12709 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12709 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12709 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12709 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12709 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12709 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12709 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12709 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12709 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12709 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12709 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12709 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12709 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12709 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052465524399 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12709) ≤ 0.010593392015 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12709 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035796427939)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010593392015 + 2 * 0.737676 / 12709) := by gcongr
    _ ≤ (0.052465524399 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12709 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12709

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12709
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560503975009 : ℝ) ≤ plow 12709 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12709) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052765366621)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379366915) : eMP 12709 0.011 xi bn ≤ 0.001187520719 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12709 : ℝ) * (1 - 0.011))) ≤ 0.000587166173 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001379366915 / (12709 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587166173 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587166173 : ℝ) + 3.141593 * 0.052765366621 / (12709 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001187520719 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052765366621)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379366915) : PiBarMP 12709 12 0.011 xi bn ≤ 0.161193461440 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12709 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037139829227 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.112448015374 : ℝ) ≤ √((12709 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.734200666878 : ℝ) ≤ √(12709 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12709) ≤ 0.123586348955 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037139829227 + 0.052765366621 * 1.772454 / (2 * (112.112448015374 : ℝ))) * (1 + 0.001187520719) +
        8 / (12709 * 112.734200666878) + 0.123586348955 := by gcongr
    _ ≤ (0.161193461440 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052765366621)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379366915) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282172656681) :
    parallelOracle 12709 0.011 xi bn cd ≤ 0.162183410953 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12709 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12709 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560503975009 : ℝ) ≤ plow 12709 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.734200666878 : ℝ) ≤ √(12709 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282172656681 : ℝ) / (2 * 0.560503975009 * 112.734200666878)) * 0.161193461440 +
        0.282172656681 ^ 2 / (2 * 0.560503975009 * 112.734200666878) := by gcongr
    _ ≤ (0.162183410953 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052765366621) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379366915)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282172656681) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12709 12709 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560503975009 : ℝ) ≤ plow 12709 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.734200666878 : ℝ) ≤ √(12709 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12709 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12709 Θ 1.22 ≤ 0.011763071829 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.734200666878 := by gcongr <;> linarith
      _ ≤ (0.011763071829 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12709 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12709 12709 0.011 ≤ 0.008479121871 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12709 12709 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12709 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12709 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12709 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12709 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162183410953 + 0.011763071829 + (0.008479121871 : ℝ) *
        (1 + 2 * (0.282172656681 + 0.011763071829) / (0.560503975009 * 112.734200666878))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12709]

end BstLean.Part269.N12709

/-! The original eight local profiles supply actual 12709 moment certificates. -/
namespace BstLean.Part269.N12709
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12709 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12709 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12709 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052765366621 ∧
    0 ≤ bN 12709 BstLean.Part154.csC (groupTheta g) ∧ bN 12709 BstLean.Part154.csC (groupTheta g) ≤ 0.001379366915 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12709 12709 0.011
      (momentAllowance 12709 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12709 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12709 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12709 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12709 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12709 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229707132282 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12709 0.011
      (momentAllowance 12709 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12709 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12709
/-! The actual computed-centre upper energy formula at 12709. -/
namespace BstLean.Part269.N12709
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12709

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12709
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12709)
open BstLean.Part268 (cell12709)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085464053327
  | 2 => 0.086406322179
  | 3 => 0.087346660737
  | 4 => 0.088286470941
  | 5 => 0.089227449047
  | 6 => 0.090171629408
  | 7 => 0.091121432392
  | 8 => 0.092079716472
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12709 12709 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12709 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003533030491 + 0.003293667169 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S14.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12709

/-! Actual upper energy certificates on all 43 source endpoints at 12709. -/
namespace BstLean.Part269.N12709
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12709)
open BstLean.Part268 (cell12709)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12709 (gMinus 12709) (1 - (cell12709 i).lower) ≤ 1 ∧
    energyUpper 12709 (gMinus 12709) (BstLean.Part211.gPlus 12709)
      (finiteEnergy 12709 12709 0.011) (1 - (cell12709 i).lower) ≤
      (cell12709 i).energy := by
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨10,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨11,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨12,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨13,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨14,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨15,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨16,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨17,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨18,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨19,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨20,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨21,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨22,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨23,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨24,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨25,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨26,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨27,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨28,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨29,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨30,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨31,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨32,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨33,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨34,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨35,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨36,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨37,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨38,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨39,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨40,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨41,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨42,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨43,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨44,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨45,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨46,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨47,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨48,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨49,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨50,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨51,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12709) (by norm_num)
        (q := 1 - (cell12709 ⟨52,by decide⟩).lower)
        (by norm_num [cell12709]) (by norm_num [cell12709])
      exact ⟨E.1,E.2.trans (by norm_num [cell12709])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12709

/-! Source-cell containment and simple scalar guards at 12709. -/
namespace BstLean.Part269.N12709
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12709)
open BstLean.Part268 (cell12709)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12709 ⟨10,by decide⟩).lower ∧ (cell12709 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12709 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12709 ⟨11,by decide⟩).lower ∧ (cell12709 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12709 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12709 ⟨12,by decide⟩).lower ∧ (cell12709 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12709 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12709 ⟨13,by decide⟩).lower ∧ (cell12709 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12709 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12709 ⟨14,by decide⟩).lower ∧ (cell12709 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12709 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12709 ⟨15,by decide⟩).lower ∧ (cell12709 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12709 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12709 ⟨16,by decide⟩).lower ∧ (cell12709 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12709 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12709 ⟨17,by decide⟩).lower ∧ (cell12709 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12709 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12709 ⟨18,by decide⟩).lower ∧ (cell12709 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12709 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12709 ⟨19,by decide⟩).lower ∧ (cell12709 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12709 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12709 ⟨20,by decide⟩).lower ∧ (cell12709 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12709 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12709 ⟨21,by decide⟩).lower ∧ (cell12709 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12709 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12709 ⟨22,by decide⟩).lower ∧ (cell12709 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12709 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12709 ⟨23,by decide⟩).lower ∧ (cell12709 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12709 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12709 ⟨24,by decide⟩).lower ∧ (cell12709 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12709 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12709 ⟨25,by decide⟩).lower ∧ (cell12709 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12709 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12709 ⟨26,by decide⟩).lower ∧ (cell12709 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12709 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12709 ⟨27,by decide⟩).lower ∧ (cell12709 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12709 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12709 ⟨28,by decide⟩).lower ∧ (cell12709 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12709 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12709 ⟨29,by decide⟩).lower ∧ (cell12709 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12709 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12709 ⟨30,by decide⟩).lower ∧ (cell12709 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12709 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12709 ⟨31,by decide⟩).lower ∧ (cell12709 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12709 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12709 ⟨32,by decide⟩).lower ∧ (cell12709 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12709 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12709 ⟨33,by decide⟩).lower ∧ (cell12709 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12709 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12709 ⟨34,by decide⟩).lower ∧ (cell12709 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12709 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12709 ⟨35,by decide⟩).lower ∧ (cell12709 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12709 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12709 ⟨36,by decide⟩).lower ∧ (cell12709 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12709 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12709 ⟨37,by decide⟩).lower ∧ (cell12709 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12709 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12709 ⟨38,by decide⟩).lower ∧ (cell12709 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12709 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12709 ⟨39,by decide⟩).lower ∧ (cell12709 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12709 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12709 ⟨40,by decide⟩).lower ∧ (cell12709 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12709 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12709 ⟨41,by decide⟩).lower ∧ (cell12709 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12709 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12709 ⟨42,by decide⟩).lower ∧ (cell12709 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12709 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12709 ⟨43,by decide⟩).lower ∧ (cell12709 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12709 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12709 ⟨44,by decide⟩).lower ∧ (cell12709 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12709 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12709 ⟨45,by decide⟩).lower ∧ (cell12709 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12709 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12709 ⟨46,by decide⟩).lower ∧ (cell12709 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12709 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12709 ⟨47,by decide⟩).lower ∧ (cell12709 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12709 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12709 ⟨48,by decide⟩).lower ∧ (cell12709 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12709 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12709 ⟨49,by decide⟩).lower ∧ (cell12709 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12709 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12709 ⟨50,by decide⟩).lower ∧ (cell12709 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12709 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12709 ⟨51,by decide⟩).lower ∧ (cell12709 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12709 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12709 ⟨52,by decide⟩).lower ∧ (cell12709 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12709 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12709 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12709 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12709,cell12709,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12709 i).lower ∧
    (cell12709 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12709 i).upper ≤ (0.532 : ℝ) ∧
    (cell12709 i).centre ≤ (0.1 : ℝ) ∧ (cell12709 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12709 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12709 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12709

/-! The local source numeric instances at 12709 have no network premises. -/
namespace BstLean.Part269.N12709
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12709)
open BstLean.Part268 (cell12709)

noncomputable def sourceNumerics12709 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12709 (cell12709 i)
      scalarRow12709.M scalarRow12709.H scalarRow12709.xi := by
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
    energy_allowance := scalarRow12709.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12709]
    centre_nonneg := (scalarRow12709.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12709])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12709
/-! Actual 12710 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12710
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12710 ≤ (1.035795007330 : ℝ) := by
  have hr : (112.738635790930 : ℝ) ≤ √(12710 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.738635790930 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12710 12710 (11 / 1000) ≤
    (0.008478788301 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12710) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.738635790930 : ℝ) ≤ √(12710 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12710)
  have hdiv : K / √(12710 : ℝ) ≤ K / 112.738635790930 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.738635790930 ≤ (0.008478788301 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12710.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12710 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12710 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12710 := gPlus_lower 12710
end BstLean.Part269.N12710

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12710
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035795007329 : ℝ) ≤ wn 12710 := by
  have hn : √(12710 : ℝ) ≤ 112.738635790931 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12710 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.738635790931 ≤ 2 / √(12710 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251679240 : ℝ) ≤ rhoBar 12710 BstLean.Part154.csC ∧
    rhoBar 12710 BstLean.Part154.csC ≤ 0.000251679630 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035795007329 : ℝ) / (1.295212 * 12710) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035795007330 : ℝ) / (1.29521 * 12710) := by gcongr
      _ ≤ (0.000251679630 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12710 BstLean.Part154.csC) ≤ 0.001006781863 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12710 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12710 BstLean.Part154.csC) (piBar (rhoBar 12710 BstLean.Part154.csC)) ≤ 0.000192234592 ∧
    cc1 (rhoBar 12710 BstLean.Part154.csC) (piBar (rhoBar 12710 BstLean.Part154.csC)) ≤ 0.000122320149 ∧
    cc2 (rhoBar 12710 BstLean.Part154.csC) ≤ 0.000071007785 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12710 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12710 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12710 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12710 BstLean.Part154.csC * nuR (rhoBar 12710 BstLean.Part154.csC)) ≤ 0.000503375096 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251679630 : ℝ) * 0.001006781863 := by gcongr
      _ ≤ (0.000503375096 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12710 BstLean.Part154.csC) * nuR (rhoBar 12710 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001006781863 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12710 BstLean.Part154.csC) * rhoBar 12710 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251679630 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251679630 / 2 + 0.399 * 0.001006781863 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192234592 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503375096 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122320149 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251679630 / 1.414213562 := by gcongr
      _ ≤ (0.000071007785 : ℝ) := by norm_num

end BstLean.Part269.N12710

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12710
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12710 BstLean.Part154.csC) (piBar (rhoBar 12710 BstLean.Part154.csC)) ≤ 1.59587E-7 := by
  have hr0 : 0 ≤ rhoBar 12710 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12710 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12710 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12710 BstLean.Part154.csC) (piBar (rhoBar 12710 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12710 BstLean.Part154.csC) (piBar (rhoBar 12710 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12710 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192234592 : ℝ) ^ 2 + 0.000122320149 ^ 2 + 3 * 0.000071007785 ^ 2 +
        2 * 0.797885 * 0.000192234592 * 0.000122320149 + 2 * 0.000192234592 * 0.000071007785 +
        4 * 0.797885 * 0.000122320149 * 0.000071007785 := by gcongr
    _ ≤ (1.59587E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12710 BstLean.Part154.csC Θ ≤ 0.002627144263 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12710 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12710 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12710 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12710 BstLean.Part154.csC) (piBar (rhoBar 12710 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12710 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035795007330 * 1.59587E-7 / (0.000251679240 : ℝ) := by gcongr
    _ ≤ 0.002627144263 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12710 BstLean.Part154.csC Θ ≤ 0.002914922563 + 0.000663837963 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12710 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12710 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12710 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035795007330 : ℝ) * ((2 * Θ * 0.000251679630 +
        (6863 / 10000) * 0.000251679630 * 12710 * 0.001006781863) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002914922563 + 0.000663837963 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12710 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12710 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12710 0.011 Θ ∧ gammaRatio 12710 0.011 Θ ≤ 0.000086520949 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12710 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035795007330 : ℝ) * 0.525 / ((1 - 0.011) * 12710) := by gcongr
      _ ≤ (0.000086520949 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12710 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12710 0.011 Θ) :=
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
    badAllowance 12710 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12710 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12710 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12710 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12710 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12710 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12710 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12710 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12710 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12710 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12710 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035795007330 : ℝ) * 12710 *
        (2.2721E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12710 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003530615040 + 0.003290982226 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12710

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12710
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12710 BstLean.Part154.csC) (piBar (rhoBar 12710 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12710 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12710 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12710 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12710 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12710 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12710 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12710 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12710 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12710 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12710 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12710 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12710 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12710 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12710 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052463438038 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12710) ≤ 0.010592975272 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12710 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035795007330)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010592975272 + 2 * 0.737676 / 12710) := by gcongr
    _ ≤ (0.052463438038 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12710 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12710

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12710
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504020165 : ℝ) ≤ plow 12710 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12710) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052764980709)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379250739) : eMP 12710 0.011 xi bn ≤ 0.001187423933 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12710 : ℝ) * (1 - 0.011))) ≤ 0.000587118347 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001379250739 / (12710 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587118347 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587118347 : ℝ) + 3.141593 * 0.052764980709 / (12710 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001187423933 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052764980709)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379250739) : PiBarMP 12710 12 0.011 xi bn ≤ 0.161187009868 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12710 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037138265159 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.116858678791 : ℝ) ≤ √((12710 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.738635790930 : ℝ) ≤ √(12710 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12710) ≤ 0.123581487084 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037138265159 + 0.052764980709 * 1.772454 / (2 * (112.116858678791 : ℝ))) * (1 + 0.001187423933) +
        8 / (12710 * 112.738635790930) + 0.123581487084 := by gcongr
    _ ≤ (0.161187009868 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052764980709)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379250739) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282169730310) :
    parallelOracle 12710 0.011 xi bn cd ≤ 0.162176889153 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12710 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12710 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504020165 : ℝ) ≤ plow 12710 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.738635790930 : ℝ) ≤ √(12710 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282169730310 : ℝ) / (2 * 0.560504020165 * 112.738635790930)) * 0.161187009868 +
        0.282169730310 ^ 2 / (2 * 0.560504020165 * 112.738635790930) := by gcongr
    _ ≤ (0.162176889153 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052764980709) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379250739)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282169730310) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12710 12710 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504020165 : ℝ) ≤ plow 12710 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.738635790930 : ℝ) ≤ √(12710 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12710 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12710 Θ 1.22 ≤ 0.011762609071 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.738635790930 := by gcongr <;> linarith
      _ ≤ (0.011762609071 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12710 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12710 12710 0.011 ≤ 0.008478788301 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12710 12710 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12710 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12710 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12710 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12710 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162176889153 + 0.011762609071 + (0.008478788301 : ℝ) *
        (1 + 2 * (0.282169730310 + 0.011762609071) / (0.560504020165 * 112.738635790930))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12710]

end BstLean.Part269.N12710

/-! The original eight local profiles supply actual 12710 moment certificates. -/
namespace BstLean.Part269.N12710
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12710 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12710 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12710 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052764980709 ∧
    0 ≤ bN 12710 BstLean.Part154.csC (groupTheta g) ∧ bN 12710 BstLean.Part154.csC (groupTheta g) ≤ 0.001379250739 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12710 12710 0.011
      (momentAllowance 12710 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12710 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12710 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12710 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12710 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12710 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229706292272 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12710 0.011
      (momentAllowance 12710 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12710 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12710
/-! The actual computed-centre upper energy formula at 12710. -/
namespace BstLean.Part269.N12710
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12710

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12710
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12710)
open BstLean.Part268 (cell12710)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085461147280
  | 2 => 0.086403362974
  | 3 => 0.087343640656
  | 4 => 0.088283380486
  | 5 => 0.089224276625
  | 6 => 0.090168360976
  | 7 => 0.091118051064
  | 8 => 0.092076202075
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12710 12710 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12710 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003533030491 + 0.003293667169 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S14.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12710

/-! Actual upper energy certificates on all 43 source endpoints at 12710. -/
namespace BstLean.Part269.N12710
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12710)
open BstLean.Part268 (cell12710)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12710 (gMinus 12710) (1 - (cell12710 i).lower) ≤ 1 ∧
    energyUpper 12710 (gMinus 12710) (BstLean.Part211.gPlus 12710)
      (finiteEnergy 12710 12710 0.011) (1 - (cell12710 i).lower) ≤
      (cell12710 i).energy := by
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨10,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨11,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨12,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨13,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨14,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨15,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨16,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨17,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨18,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨19,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨20,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨21,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨22,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨23,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨24,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨25,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨26,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨27,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨28,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨29,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨30,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨31,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨32,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨33,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨34,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨35,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨36,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨37,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨38,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨39,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨40,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨41,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨42,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨43,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨44,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨45,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨46,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨47,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨48,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨49,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨50,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨51,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12710) (by norm_num)
        (q := 1 - (cell12710 ⟨52,by decide⟩).lower)
        (by norm_num [cell12710]) (by norm_num [cell12710])
      exact ⟨E.1,E.2.trans (by norm_num [cell12710])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12710

/-! Source-cell containment and simple scalar guards at 12710. -/
namespace BstLean.Part269.N12710
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12710)
open BstLean.Part268 (cell12710)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12710 ⟨10,by decide⟩).lower ∧ (cell12710 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12710 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12710 ⟨11,by decide⟩).lower ∧ (cell12710 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12710 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12710 ⟨12,by decide⟩).lower ∧ (cell12710 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12710 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12710 ⟨13,by decide⟩).lower ∧ (cell12710 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12710 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12710 ⟨14,by decide⟩).lower ∧ (cell12710 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12710 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12710 ⟨15,by decide⟩).lower ∧ (cell12710 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12710 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12710 ⟨16,by decide⟩).lower ∧ (cell12710 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12710 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12710 ⟨17,by decide⟩).lower ∧ (cell12710 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12710 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12710 ⟨18,by decide⟩).lower ∧ (cell12710 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12710 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12710 ⟨19,by decide⟩).lower ∧ (cell12710 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12710 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12710 ⟨20,by decide⟩).lower ∧ (cell12710 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12710 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12710 ⟨21,by decide⟩).lower ∧ (cell12710 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12710 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12710 ⟨22,by decide⟩).lower ∧ (cell12710 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12710 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12710 ⟨23,by decide⟩).lower ∧ (cell12710 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12710 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12710 ⟨24,by decide⟩).lower ∧ (cell12710 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12710 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12710 ⟨25,by decide⟩).lower ∧ (cell12710 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12710 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12710 ⟨26,by decide⟩).lower ∧ (cell12710 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12710 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12710 ⟨27,by decide⟩).lower ∧ (cell12710 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12710 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12710 ⟨28,by decide⟩).lower ∧ (cell12710 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12710 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12710 ⟨29,by decide⟩).lower ∧ (cell12710 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12710 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12710 ⟨30,by decide⟩).lower ∧ (cell12710 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12710 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12710 ⟨31,by decide⟩).lower ∧ (cell12710 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12710 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12710 ⟨32,by decide⟩).lower ∧ (cell12710 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12710 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12710 ⟨33,by decide⟩).lower ∧ (cell12710 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12710 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12710 ⟨34,by decide⟩).lower ∧ (cell12710 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12710 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12710 ⟨35,by decide⟩).lower ∧ (cell12710 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12710 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12710 ⟨36,by decide⟩).lower ∧ (cell12710 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12710 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12710 ⟨37,by decide⟩).lower ∧ (cell12710 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12710 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12710 ⟨38,by decide⟩).lower ∧ (cell12710 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12710 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12710 ⟨39,by decide⟩).lower ∧ (cell12710 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12710 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12710 ⟨40,by decide⟩).lower ∧ (cell12710 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12710 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12710 ⟨41,by decide⟩).lower ∧ (cell12710 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12710 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12710 ⟨42,by decide⟩).lower ∧ (cell12710 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12710 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12710 ⟨43,by decide⟩).lower ∧ (cell12710 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12710 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12710 ⟨44,by decide⟩).lower ∧ (cell12710 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12710 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12710 ⟨45,by decide⟩).lower ∧ (cell12710 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12710 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12710 ⟨46,by decide⟩).lower ∧ (cell12710 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12710 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12710 ⟨47,by decide⟩).lower ∧ (cell12710 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12710 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12710 ⟨48,by decide⟩).lower ∧ (cell12710 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12710 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12710 ⟨49,by decide⟩).lower ∧ (cell12710 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12710 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12710 ⟨50,by decide⟩).lower ∧ (cell12710 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12710 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12710 ⟨51,by decide⟩).lower ∧ (cell12710 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12710 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12710 ⟨52,by decide⟩).lower ∧ (cell12710 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12710 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12710 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12710 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12710,cell12710,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12710 i).lower ∧
    (cell12710 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12710 i).upper ≤ (0.532 : ℝ) ∧
    (cell12710 i).centre ≤ (0.1 : ℝ) ∧ (cell12710 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12710 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12710 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12710

/-! The local source numeric instances at 12710 have no network premises. -/
namespace BstLean.Part269.N12710
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12710)
open BstLean.Part268 (cell12710)

noncomputable def sourceNumerics12710 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12710 (cell12710 i)
      scalarRow12710.M scalarRow12710.H scalarRow12710.xi := by
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
    energy_allowance := scalarRow12710.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12710]
    centre_nonneg := (scalarRow12710.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12710])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12710
/-! Actual 12711 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12711
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12711 ≤ (1.035793586891 : ℝ) := by
  have hr : (112.743070740511 : ℝ) ≤ √(12711 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.743070740511 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12711 12711 (11 / 1000) ≤
    (0.008478454770 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12711) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.743070740511 : ℝ) ≤ √(12711 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12711)
  have hdiv : K / √(12711 : ℝ) ≤ K / 112.743070740511 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.743070740511 ≤ (0.008478454770 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12711.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12711 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12711 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12711 := gPlus_lower 12711
end BstLean.Part269.N12711

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12711
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035793586890 : ℝ) ≤ wn 12711 := by
  have hn : √(12711 : ℝ) ≤ 112.743070740512 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12711 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.743070740512 ≤ 2 / √(12711 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251659095 : ℝ) ≤ rhoBar 12711 BstLean.Part154.csC ∧
    rhoBar 12711 BstLean.Part154.csC ≤ 0.000251659484 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035793586890 : ℝ) / (1.295212 * 12711) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035793586891 : ℝ) / (1.29521 * 12711) := by gcongr
      _ ≤ (0.000251659484 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12711 BstLean.Part154.csC) ≤ 0.001006701269 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12711 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12711 BstLean.Part154.csC) (piBar (rhoBar 12711 BstLean.Part154.csC)) ≤ 0.000192219204 ∧
    cc1 (rhoBar 12711 BstLean.Part154.csC) (piBar (rhoBar 12711 BstLean.Part154.csC)) ≤ 0.000122310357 ∧
    cc2 (rhoBar 12711 BstLean.Part154.csC) ≤ 0.000071002101 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12711 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12711 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12711 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12711 BstLean.Part154.csC * nuR (rhoBar 12711 BstLean.Part154.csC)) ≤ 0.000503334802 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251659484 : ℝ) * 0.001006701269 := by gcongr
      _ ≤ (0.000503334802 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12711 BstLean.Part154.csC) * nuR (rhoBar 12711 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001006701269 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12711 BstLean.Part154.csC) * rhoBar 12711 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251659484 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251659484 / 2 + 0.399 * 0.001006701269 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192219204 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503334802 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122310357 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251659484 / 1.414213562 := by gcongr
      _ ≤ (0.000071002101 : ℝ) := by norm_num

end BstLean.Part269.N12711

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12711
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12711 BstLean.Part154.csC) (piBar (rhoBar 12711 BstLean.Part154.csC)) ≤ 1.59562E-7 := by
  have hr0 : 0 ≤ rhoBar 12711 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12711 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12711 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12711 BstLean.Part154.csC) (piBar (rhoBar 12711 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12711 BstLean.Part154.csC) (piBar (rhoBar 12711 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12711 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192219204 : ℝ) ^ 2 + 0.000122310357 ^ 2 + 3 * 0.000071002101 ^ 2 +
        2 * 0.797885 * 0.000192219204 * 0.000122310357 + 2 * 0.000192219204 * 0.000071002101 +
        4 * 0.797885 * 0.000122310357 * 0.000071002101 := by gcongr
    _ ≤ (1.59562E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12711 BstLean.Part154.csC Θ ≤ 0.002626939374 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12711 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12711 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12711 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12711 BstLean.Part154.csC) (piBar (rhoBar 12711 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12711 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035793586891 * 1.59562E-7 / (0.000251659095 : ℝ) := by gcongr
    _ ≤ 0.002626939374 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12711 BstLean.Part154.csC Θ ≤ 0.002914681217 + 0.000663783915 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12711 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12711 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12711 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035793586891 : ℝ) * ((2 * Θ * 0.000251659484 +
        (6863 / 10000) * 0.000251659484 * 12711 * 0.001006701269) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002914681217 + 0.000663783915 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12711 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12711 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12711 0.011 Θ ∧ gammaRatio 12711 0.011 Θ ≤ 0.000086514023 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12711 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035793586891 : ℝ) * 0.525 / ((1 - 0.011) * 12711) := by gcongr
      _ ≤ (0.000086514023 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12711 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12711 0.011 Θ) :=
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
    badAllowance 12711 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12711 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12711 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12711 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12711 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12711 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12711 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12711 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12711 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12711 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12711 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035793586891 : ℝ) * 12711 *
        (2.2721E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12711 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003530373694 + 0.003290723289 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12711

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12711
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12711 BstLean.Part154.csC) (piBar (rhoBar 12711 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12711 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12711 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12711 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12711 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12711 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12711 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12711 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12711 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12711 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12711 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12711 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12711 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12711 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12711 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052461351924 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12711) ≤ 0.010592558578 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12711 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035793586891)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010592558578 + 2 * 0.737676 / 12711) := by gcongr
    _ ≤ (0.052461351924 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12711 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12711

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12711
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504065313 : ℝ) ≤ plow 12711 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12711) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052764603421)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379143172) : eMP 12711 0.011 xi bn ≤ 0.001187330823 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12711 : ℝ) * (1 - 0.011))) ≤ 0.000587072358 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001379143172 / (12711 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587072358 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587072358 : ℝ) + 3.141593 * 0.052764603421 / (12711 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001187330823 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052764603421)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379143172) : PiBarMP 12711 12 0.011 xi bn ≤ 0.161180675059 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12711 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037136816935 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.121269168699 : ℝ) ≤ √((12711 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.743070740511 : ℝ) ≤ √(12711 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12711) ≤ 0.123576625786 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037136816935 + 0.052764603421 * 1.772454 / (2 * (112.121269168699 : ℝ))) * (1 + 0.001187330823) +
        8 / (12711 * 112.743070740511) + 0.123576625786 := by gcongr
    _ ≤ (0.161180675059 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052764603421)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379143172) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282166822954) :
    parallelOracle 12711 0.011 xi bn cd ≤ 0.162170484492 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12711 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12711 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504065313 : ℝ) ≤ plow 12711 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.743070740511 : ℝ) ≤ √(12711 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282166822954 : ℝ) / (2 * 0.560504065313 * 112.743070740511)) * 0.161180675059 +
        0.282166822954 ^ 2 / (2 * 0.560504065313 * 112.743070740511) := by gcongr
    _ ≤ (0.162170484492 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052764603421) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379143172)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282166822954) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12711 12711 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504065313 : ℝ) ≤ plow 12711 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.743070740511 : ℝ) ≤ √(12711 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12711 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12711 Θ 1.22 ≤ 0.011762146368 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.743070740511 := by gcongr <;> linarith
      _ ≤ (0.011762146368 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12711 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12711 12711 0.011 ≤ 0.008478454770 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12711 12711 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12711 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12711 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12711 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12711 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162170484492 + 0.011762146368 + (0.008478454770 : ℝ) *
        (1 + 2 * (0.282166822954 + 0.011762146368) / (0.560504065313 * 112.743070740511))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12711]

end BstLean.Part269.N12711

/-! The original eight local profiles supply actual 12711 moment certificates. -/
namespace BstLean.Part269.N12711
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12711 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12711 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12711 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052764603421 ∧
    0 ≤ bN 12711 BstLean.Part154.csC (groupTheta g) ∧ bN 12711 BstLean.Part154.csC (groupTheta g) ≤ 0.001379143172 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12711 12711 0.011
      (momentAllowance 12711 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12711 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12711 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12711 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12711 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12711 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229705471030 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12711 0.011
      (momentAllowance 12711 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12711 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12711
/-! The actual computed-centre upper energy formula at 12711. -/
namespace BstLean.Part269.N12711
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12711

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12711
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12711)
open BstLean.Part268 (cell12711)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085458242307
  | 2 => 0.086400404886
  | 3 => 0.087340621746
  | 4 => 0.088280291269
  | 5 => 0.089221105522
  | 6 => 0.090165093963
  | 7 => 0.091114671273
  | 8 => 0.092072689361
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12711 12711 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12711 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003533030491 + 0.003293667169 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S14.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12711

/-! Actual upper energy certificates on all 43 source endpoints at 12711. -/
namespace BstLean.Part269.N12711
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12711)
open BstLean.Part268 (cell12711)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12711 (gMinus 12711) (1 - (cell12711 i).lower) ≤ 1 ∧
    energyUpper 12711 (gMinus 12711) (BstLean.Part211.gPlus 12711)
      (finiteEnergy 12711 12711 0.011) (1 - (cell12711 i).lower) ≤
      (cell12711 i).energy := by
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨10,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨11,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨12,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨13,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨14,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨15,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨16,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨17,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨18,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨19,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨20,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨21,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨22,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨23,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨24,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨25,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨26,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨27,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨28,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨29,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨30,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨31,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨32,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨33,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨34,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨35,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨36,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨37,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨38,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨39,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨40,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨41,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨42,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨43,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨44,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨45,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨46,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨47,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨48,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨49,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨50,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨51,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12711) (by norm_num)
        (q := 1 - (cell12711 ⟨52,by decide⟩).lower)
        (by norm_num [cell12711]) (by norm_num [cell12711])
      exact ⟨E.1,E.2.trans (by norm_num [cell12711])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12711

/-! Source-cell containment and simple scalar guards at 12711. -/
namespace BstLean.Part269.N12711
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12711)
open BstLean.Part268 (cell12711)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12711 ⟨10,by decide⟩).lower ∧ (cell12711 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12711 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12711 ⟨11,by decide⟩).lower ∧ (cell12711 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12711 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12711 ⟨12,by decide⟩).lower ∧ (cell12711 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12711 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12711 ⟨13,by decide⟩).lower ∧ (cell12711 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12711 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12711 ⟨14,by decide⟩).lower ∧ (cell12711 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12711 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12711 ⟨15,by decide⟩).lower ∧ (cell12711 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12711 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12711 ⟨16,by decide⟩).lower ∧ (cell12711 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12711 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12711 ⟨17,by decide⟩).lower ∧ (cell12711 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12711 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12711 ⟨18,by decide⟩).lower ∧ (cell12711 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12711 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12711 ⟨19,by decide⟩).lower ∧ (cell12711 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12711 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12711 ⟨20,by decide⟩).lower ∧ (cell12711 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12711 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12711 ⟨21,by decide⟩).lower ∧ (cell12711 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12711 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12711 ⟨22,by decide⟩).lower ∧ (cell12711 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12711 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12711 ⟨23,by decide⟩).lower ∧ (cell12711 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12711 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12711 ⟨24,by decide⟩).lower ∧ (cell12711 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12711 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12711 ⟨25,by decide⟩).lower ∧ (cell12711 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12711 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12711 ⟨26,by decide⟩).lower ∧ (cell12711 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12711 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12711 ⟨27,by decide⟩).lower ∧ (cell12711 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12711 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12711 ⟨28,by decide⟩).lower ∧ (cell12711 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12711 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12711 ⟨29,by decide⟩).lower ∧ (cell12711 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12711 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12711 ⟨30,by decide⟩).lower ∧ (cell12711 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12711 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12711 ⟨31,by decide⟩).lower ∧ (cell12711 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12711 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12711 ⟨32,by decide⟩).lower ∧ (cell12711 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12711 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12711 ⟨33,by decide⟩).lower ∧ (cell12711 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12711 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12711 ⟨34,by decide⟩).lower ∧ (cell12711 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12711 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12711 ⟨35,by decide⟩).lower ∧ (cell12711 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12711 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12711 ⟨36,by decide⟩).lower ∧ (cell12711 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12711 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12711 ⟨37,by decide⟩).lower ∧ (cell12711 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12711 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12711 ⟨38,by decide⟩).lower ∧ (cell12711 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12711 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12711 ⟨39,by decide⟩).lower ∧ (cell12711 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12711 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12711 ⟨40,by decide⟩).lower ∧ (cell12711 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12711 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12711 ⟨41,by decide⟩).lower ∧ (cell12711 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12711 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12711 ⟨42,by decide⟩).lower ∧ (cell12711 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12711 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12711 ⟨43,by decide⟩).lower ∧ (cell12711 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12711 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12711 ⟨44,by decide⟩).lower ∧ (cell12711 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12711 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12711 ⟨45,by decide⟩).lower ∧ (cell12711 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12711 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12711 ⟨46,by decide⟩).lower ∧ (cell12711 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12711 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12711 ⟨47,by decide⟩).lower ∧ (cell12711 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12711 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12711 ⟨48,by decide⟩).lower ∧ (cell12711 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12711 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12711 ⟨49,by decide⟩).lower ∧ (cell12711 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12711 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12711 ⟨50,by decide⟩).lower ∧ (cell12711 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12711 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12711 ⟨51,by decide⟩).lower ∧ (cell12711 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12711 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12711 ⟨52,by decide⟩).lower ∧ (cell12711 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12711 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12711 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12711 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12711,cell12711,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12711 i).lower ∧
    (cell12711 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12711 i).upper ≤ (0.532 : ℝ) ∧
    (cell12711 i).centre ≤ (0.1 : ℝ) ∧ (cell12711 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12711 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12711 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12711

/-! The local source numeric instances at 12711 have no network premises. -/
namespace BstLean.Part269.N12711
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12711)
open BstLean.Part268 (cell12711)

noncomputable def sourceNumerics12711 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12711 (cell12711 i)
      scalarRow12711.M scalarRow12711.H scalarRow12711.xi := by
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
    energy_allowance := scalarRow12711.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12711]
    centre_nonneg := (scalarRow12711.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12711])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12711
/-! Actual 12712 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12712
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12712 ≤ (1.035792166620 : ℝ) := by
  have hr : (112.747505515643 : ℝ) ≤ √(12712 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (112.747505515643 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12712 12712 (11 / 1000) ≤
    (0.008478121279 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12712) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (112.747505515643 : ℝ) ≤ √(12712 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12712)
  have hdiv : K / √(12712 : ℝ) ≤ K / 112.747505515643 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 112.747505515643 ≤ (0.008478121279 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12712.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12712 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12712 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12712 := gPlus_lower 12712
end BstLean.Part269.N12712

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12712
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035792166619 : ℝ) ≤ wn 12712 := by
  have hn : √(12712 : ℝ) ≤ 112.747505515644 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12712 : ℝ) := by positivity
  have hd : (2 : ℝ) / 112.747505515644 ≤ 2 / √(12712 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000251638953 : ℝ) ≤ rhoBar 12712 BstLean.Part154.csC ∧
    rhoBar 12712 BstLean.Part154.csC ≤ 0.000251639342 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035792166619 : ℝ) / (1.295212 * 12712) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035792166620 : ℝ) / (1.29521 * 12712) := by gcongr
      _ ≤ (0.000251639342 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12712 BstLean.Part154.csC) ≤ 0.001006620691 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12712 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12712 BstLean.Part154.csC) (piBar (rhoBar 12712 BstLean.Part154.csC)) ≤ 0.000192203818 ∧
    cc1 (rhoBar 12712 BstLean.Part154.csC) (piBar (rhoBar 12712 BstLean.Part154.csC)) ≤ 0.000122300568 ∧
    cc2 (rhoBar 12712 BstLean.Part154.csC) ≤ 0.000070996419 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12712 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12712 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12712 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12712 BstLean.Part154.csC * nuR (rhoBar 12712 BstLean.Part154.csC)) ≤ 0.000503294515 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000251639342 : ℝ) * 0.001006620691 := by gcongr
      _ ≤ (0.000503294515 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12712 BstLean.Part154.csC) * nuR (rhoBar 12712 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001006620691 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12712 BstLean.Part154.csC) * rhoBar 12712 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000251639342 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000251639342 / 2 + 0.399 * 0.001006620691 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000192203818 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000503294515 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000122300568 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000251639342 / 1.414213562 := by gcongr
      _ ≤ (0.000070996419 : ℝ) := by norm_num

end BstLean.Part269.N12712

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12712
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12712 BstLean.Part154.csC) (piBar (rhoBar 12712 BstLean.Part154.csC)) ≤ 1.59536E-7 := by
  have hr0 : 0 ≤ rhoBar 12712 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12712 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12712 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12712 BstLean.Part154.csC) (piBar (rhoBar 12712 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12712 BstLean.Part154.csC) (piBar (rhoBar 12712 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12712 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000192203818 : ℝ) ^ 2 + 0.000122300568 ^ 2 + 3 * 0.000070996419 ^ 2 +
        2 * 0.797885 * 0.000192203818 * 0.000122300568 + 2 * 0.000192203818 * 0.000070996419 +
        4 * 0.797885 * 0.000122300568 * 0.000070996419 := by gcongr
    _ ≤ (1.59536E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12712 BstLean.Part154.csC Θ ≤ 0.002626717957 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12712 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12712 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12712 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12712 BstLean.Part154.csC) (piBar (rhoBar 12712 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12712 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035792166620 * 1.59536E-7 / (0.000251638953 : ℝ) := by gcongr
    _ ≤ 0.002626717957 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12712 BstLean.Part154.csC Θ ≤ 0.002914439929 + 0.000663729878 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12712 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12712 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12712 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035792166620 : ℝ) * ((2 * Θ * 0.000251639342 +
        (6863 / 10000) * 0.000251639342 * 12712 * 0.001006620691) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002914439929 + 0.000663729878 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12712 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12712 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12712 0.011 Θ ∧ gammaRatio 12712 0.011 Θ ≤ 0.000086507099 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12712 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035792166620 : ℝ) * 0.525 / ((1 - 0.011) * 12712) := by gcongr
      _ ≤ (0.000086507099 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12712 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12712 0.011 Θ) :=
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
    badAllowance 12712 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000615692477 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12712 BstLean.Part154.csC) 1.22 ≤ 2.2721E-8 := by
    have he : (17.6 : ℝ) ≤ gap 2 (rhoBar 12712 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12712 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12712 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_6_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12712 0.011 Θ) 1.12 ≤ 2.5110E-8 := by
    have he : (17.5 : ℝ) ≤ gap 1 (gammaRatio 12712 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12712 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12712 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_5_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12712 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12712 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035792166620 : ℝ) * 12712 *
        (2.2721E-8 / 1.1045361 + 2.5110E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000615692477 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12712 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003530132406 + 0.003290447835 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12712

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12712
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12712 BstLean.Part154.csC) (piBar (rhoBar 12712 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12712 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12712 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12712 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12712 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12712 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12712 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12712 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12712 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12712 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12712 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12712 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12712 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12712 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12712 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052459266063 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12712) ≤ 0.010592141934 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12712 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035792166620)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010592141934 + 2 * 0.737676 / 12712) := by gcongr
    _ ≤ (0.052459266063 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12712 12 ≤ 0.0015 := by
  exact BstLean.Part269.S14.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12712

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12712
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560504110454 : ℝ) ≤ plow 12712 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12712) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052764217520)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379026928) : eMP 12712 0.011 xi bn ≤ 0.001187234024 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12712 : ℝ) * (1 - 0.011))) ≤ 0.000587024525 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001379026928 / (12712 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000587024525 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000587024525 : ℝ) + 3.141593 * 0.052764217520 / (12712 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001187234024 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052764217520)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379026928) : PiBarMP 12712 12 0.011 xi bn ≤ 0.161174223593 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12712 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037135251824 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (112.125679485120 : ℝ) ≤ √((12712 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (112.747505515643 : ℝ) ≤ √(12712 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12712) ≤ 0.123571765061 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037135251824 + 0.052764217520 * 1.772454 / (2 * (112.125679485120 : ℝ))) * (1 + 0.001187234024) +
        8 / (12712 * 112.747505515643) + 0.123571765061 := by gcongr
    _ ≤ (0.161174223593 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052764217520)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379026928) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282163897101) :
    parallelOracle 12712 0.011 xi bn cd ≤ 0.162163962816 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12712 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12712 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560504110454 : ℝ) ≤ plow 12712 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.747505515643 : ℝ) ≤ √(12712 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.282163897101 : ℝ) / (2 * 0.560504110454 * 112.747505515643)) * 0.161174223593 +
        0.282163897101 ^ 2 / (2 * 0.560504110454 * 112.747505515643) := by gcongr
    _ ≤ (0.162163962816 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052764217520) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001379026928)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.282163897101) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12712 12712 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560504110454 : ℝ) ≤ plow 12712 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (112.747505515643 : ℝ) ≤ √(12712 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12712 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12712 Θ 1.22 ≤ 0.011761683720 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 112.747505515643 := by gcongr <;> linarith
      _ ≤ (0.011761683720 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12712 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12712 12712 0.011 ≤ 0.008478121279 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12712 12712 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12712 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12712 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12712 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12712 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.162163962816 + 0.011761683720 + (0.008478121279 : ℝ) *
        (1 + 2 * (0.282163897101 + 0.011761683720) / (0.560504110454 * 112.747505515643))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12712]

end BstLean.Part269.N12712

/-! The original eight local profiles supply actual 12712 moment certificates. -/
namespace BstLean.Part269.N12712
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12712 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12712 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12712 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052764217520 ∧
    0 ≤ bN 12712 BstLean.Part154.csC (groupTheta g) ∧ bN 12712 BstLean.Part154.csC (groupTheta g) ≤ 0.001379026928 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12712 12712 0.011
      (momentAllowance 12712 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12712 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12712 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12712 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12712 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12712 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.229704631038 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12712 0.011
      (momentAllowance 12712 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12712 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12712
/-! The actual computed-centre upper energy formula at 12712. -/
namespace BstLean.Part269.N12712
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12712

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12712
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12712)
open BstLean.Part268 (cell12712)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.085455338405
  | 2 => 0.086397447914
  | 3 => 0.087337604006
  | 4 => 0.088277203289
  | 5 => 0.089217935738
  | 6 => 0.090161828367
  | 7 => 0.091111293020
  | 8 => 0.092069178328
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12712 12712 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12712 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003533030491 + 0.003293667169 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S14.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S14.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12712

/-! Actual upper energy certificates on all 43 source endpoints at 12712. -/
namespace BstLean.Part269.N12712
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12712)
open BstLean.Part268 (cell12712)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12712 (gMinus 12712) (1 - (cell12712 i).lower) ≤ 1 ∧
    energyUpper 12712 (gMinus 12712) (BstLean.Part211.gPlus 12712)
      (finiteEnergy 12712 12712 0.011) (1 - (cell12712 i).lower) ≤
      (cell12712 i).energy := by
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
      have E := BstLean.Part269.S14.uniformEnergy10 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨10,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy11 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨11,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy12 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨12,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy13 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨13,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy14 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨14,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy15 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨15,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy16 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨16,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy17 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨17,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy18 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨18,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy19 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨19,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy20 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨20,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy21 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨21,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy22 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨22,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy23 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨23,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy24 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨24,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy25 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨25,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy26 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨26,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy27 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨27,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy28 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨28,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy29 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨29,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy30 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨30,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy31 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨31,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy32 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨32,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy33 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨33,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy34 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨34,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy35 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨35,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy36 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨36,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy37 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨37,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy38 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨38,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy39 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨39,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy40 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨40,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy41 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨41,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy42 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨42,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy43 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨43,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy44 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨44,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy45 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨45,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy46 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨46,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy47 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨47,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy48 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨48,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy49 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨49,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy50 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨50,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy51 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨51,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S14.uniformEnergy52 (n := 12712) (by norm_num)
        (q := 1 - (cell12712 ⟨52,by decide⟩).lower)
        (by norm_num [cell12712]) (by norm_num [cell12712])
      exact ⟨E.1,E.2.trans (by norm_num [cell12712])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12712

/-! Source-cell containment and simple scalar guards at 12712. -/
namespace BstLean.Part269.N12712
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12712)
open BstLean.Part268 (cell12712)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12712 ⟨10,by decide⟩).lower ∧ (cell12712 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12712 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12712 ⟨11,by decide⟩).lower ∧ (cell12712 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12712 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12712 ⟨12,by decide⟩).lower ∧ (cell12712 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12712 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12712 ⟨13,by decide⟩).lower ∧ (cell12712 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12712 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12712 ⟨14,by decide⟩).lower ∧ (cell12712 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12712 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12712 ⟨15,by decide⟩).lower ∧ (cell12712 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12712 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12712 ⟨16,by decide⟩).lower ∧ (cell12712 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12712 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12712 ⟨17,by decide⟩).lower ∧ (cell12712 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12712 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12712 ⟨18,by decide⟩).lower ∧ (cell12712 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12712 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12712 ⟨19,by decide⟩).lower ∧ (cell12712 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12712 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12712 ⟨20,by decide⟩).lower ∧ (cell12712 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12712 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12712 ⟨21,by decide⟩).lower ∧ (cell12712 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12712 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12712 ⟨22,by decide⟩).lower ∧ (cell12712 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12712 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12712 ⟨23,by decide⟩).lower ∧ (cell12712 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12712 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12712 ⟨24,by decide⟩).lower ∧ (cell12712 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12712 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12712 ⟨25,by decide⟩).lower ∧ (cell12712 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12712 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12712 ⟨26,by decide⟩).lower ∧ (cell12712 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12712 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12712 ⟨27,by decide⟩).lower ∧ (cell12712 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12712 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12712 ⟨28,by decide⟩).lower ∧ (cell12712 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12712 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12712 ⟨29,by decide⟩).lower ∧ (cell12712 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12712 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12712 ⟨30,by decide⟩).lower ∧ (cell12712 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12712 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12712 ⟨31,by decide⟩).lower ∧ (cell12712 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12712 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12712 ⟨32,by decide⟩).lower ∧ (cell12712 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12712 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12712 ⟨33,by decide⟩).lower ∧ (cell12712 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12712 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12712 ⟨34,by decide⟩).lower ∧ (cell12712 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12712 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12712 ⟨35,by decide⟩).lower ∧ (cell12712 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12712 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12712 ⟨36,by decide⟩).lower ∧ (cell12712 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12712 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12712 ⟨37,by decide⟩).lower ∧ (cell12712 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12712 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12712 ⟨38,by decide⟩).lower ∧ (cell12712 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12712 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12712 ⟨39,by decide⟩).lower ∧ (cell12712 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12712 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12712 ⟨40,by decide⟩).lower ∧ (cell12712 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12712 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12712 ⟨41,by decide⟩).lower ∧ (cell12712 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12712 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12712 ⟨42,by decide⟩).lower ∧ (cell12712 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12712 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12712 ⟨43,by decide⟩).lower ∧ (cell12712 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12712 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12712 ⟨44,by decide⟩).lower ∧ (cell12712 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12712 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12712 ⟨45,by decide⟩).lower ∧ (cell12712 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12712 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12712 ⟨46,by decide⟩).lower ∧ (cell12712 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12712 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12712 ⟨47,by decide⟩).lower ∧ (cell12712 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12712 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12712 ⟨48,by decide⟩).lower ∧ (cell12712 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12712 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12712 ⟨49,by decide⟩).lower ∧ (cell12712 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12712 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12712 ⟨50,by decide⟩).lower ∧ (cell12712 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12712 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12712 ⟨51,by decide⟩).lower ∧ (cell12712 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12712 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12712 ⟨52,by decide⟩).lower ∧ (cell12712 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12712 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12712 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12712 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12712,cell12712,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12712 i).lower ∧
    (cell12712 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12712 i).upper ≤ (0.532 : ℝ) ∧
    (cell12712 i).centre ≤ (0.1 : ℝ) ∧ (cell12712 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12712 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12712 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12712

/-! The local source numeric instances at 12712 have no network premises. -/
namespace BstLean.Part269.N12712
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12712)
open BstLean.Part268 (cell12712)

noncomputable def sourceNumerics12712 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12712 (cell12712 i)
      scalarRow12712.M scalarRow12712.H scalarRow12712.xi := by
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
    energy_allowance := scalarRow12712.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12712]
    centre_nonneg := (scalarRow12712.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D14.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12712])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12712