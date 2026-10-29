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
import BstLean.Part269Direction5
import BstLean.Part269Shared5
import BstLean.Part269Finite
import BstLean.Part269Rows5
import BstLean.Part269Source
/-! Actual 12475 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12475
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12475 ≤ (1.036133559766 : ℝ) := by
  have hr : (111.691539518443 : ℝ) ≤ √(12475 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.691539518443 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12475 12475 (11 / 1000) ≤
    (0.008558276657 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12475) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.691539518443 : ℝ) ≤ √(12475 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12475)
  have hdiv : K / √(12475 : ℝ) ≤ K / 111.691539518443 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.691539518443 ≤ (0.008558276657 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12475.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12475 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12475 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12475 := gPlus_lower 12475
end BstLean.Part269.N12475

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12475
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036133559765 : ℝ) ≤ wn 12475 := by
  have hn : √(12475 : ℝ) ≤ 111.691539518444 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12475 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.691539518444 ≤ 2 / √(12475 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256504103 : ℝ) ≤ rhoBar 12475 BstLean.Part154.csC ∧
    rhoBar 12475 BstLean.Part154.csC ≤ 0.000256504501 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036133559765 : ℝ) / (1.295212 * 12475) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036133559766 : ℝ) / (1.29521 * 12475) := by gcongr
      _ ≤ (0.000256504501 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12475 BstLean.Part154.csC) ≤ 0.001026083799 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12475 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12475 BstLean.Part154.csC) (piBar (rhoBar 12475 BstLean.Part154.csC)) ≤ 0.000195920036 ∧
    cc1 (rhoBar 12475 BstLean.Part154.csC) (piBar (rhoBar 12475 BstLean.Part154.csC)) ≤ 0.000124665185 ∧
    cc2 (rhoBar 12475 BstLean.Part154.csC) ≤ 0.000072369053 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12475 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12475 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12475 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12475 BstLean.Part154.csC * nuR (rhoBar 12475 BstLean.Part154.csC)) ≤ 0.000513025451 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256504501 : ℝ) * 0.001026083799 := by gcongr
      _ ≤ (0.000513025451 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12475 BstLean.Part154.csC) * nuR (rhoBar 12475 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001026083799 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12475 BstLean.Part154.csC) * rhoBar 12475 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256504501 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256504501 / 2 + 0.399 * 0.001026083799 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195920036 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000513025451 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124665185 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256504501 / 1.414213562 := by gcongr
      _ ≤ (0.000072369053 : ℝ) := by norm_num

end BstLean.Part269.N12475

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12475
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12475 BstLean.Part154.csC) (piBar (rhoBar 12475 BstLean.Part154.csC)) ≤ 1.65765E-7 := by
  have hr0 : 0 ≤ rhoBar 12475 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12475 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12475 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12475 BstLean.Part154.csC) (piBar (rhoBar 12475 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12475 BstLean.Part154.csC) (piBar (rhoBar 12475 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12475 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195920036 : ℝ) ^ 2 + 0.000124665185 ^ 2 + 3 * 0.000072369053 ^ 2 +
        2 * 0.797885 * 0.000195920036 * 0.000124665185 + 2 * 0.000195920036 * 0.000072369053 +
        4 * 0.797885 * 0.000124665185 * 0.000072369053 := by gcongr
    _ ≤ (1.65765E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12475 BstLean.Part154.csC Θ ≤ 0.002678392705 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12475 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12475 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12475 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12475 BstLean.Part154.csC) (piBar (rhoBar 12475 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12475 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036133559766 * 1.65765E-7 / (0.000256504103 : ℝ) := by gcongr
    _ ≤ 0.002678392705 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12475 BstLean.Part154.csC Θ ≤ 0.002972749560 + 0.000676785329 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12475 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12475 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12475 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036133559766 : ℝ) * ((2 * Θ * 0.000256504501 +
        (6863 / 10000) * 0.000256504501 * 12475 * 0.001026083799) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002972749560 + 0.000676785329 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12475 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12475 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12475 0.011 Θ ∧ gammaRatio 12475 0.011 Θ ≤ 0.000088179615 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12475 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036133559766 : ℝ) * 0.525 / ((1 - 0.011) * 12475) := by gcongr
      _ ≤ (0.000088179615 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12475 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12475 0.011 Θ) :=
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
    badAllowance 12475 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12475 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12475 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12475 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12475 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12475 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12475 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12475 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12475 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12475 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12475 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036133559766 : ℝ) * 12475 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12475 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003790088722 + 0.003355178034 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12475

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12475
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12475 BstLean.Part154.csC) (piBar (rhoBar 12475 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12475 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12475 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12475 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12475 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12475 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12475 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12475 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12475 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12475 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12475 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12475 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12475 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12475 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12475 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052960658316 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12475) ≤ 0.010692283285 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12475 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036133559766)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010692283285 + 2 * 0.737676 / 12475) := by gcongr
    _ ≤ (0.052960658316 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12475 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12475

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12475
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493209603 : ℝ) ≤ plow 12475 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12475) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053058157190)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406156171) : eMP 12475 0.011 xi bn ≤ 0.001210259966 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12475 : ℝ) * (1 - 0.011))) ≤ 0.000598374829 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001406156171 / (12475 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598374829 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598374829 : ℝ) + 3.141593 * 0.053058157190 / (12475 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001210259966 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053058157190)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406156171) : PiBarMP 12475 12 0.011 xi bn ≤ 0.162713766074 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12475 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037498748926 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.075537360842 : ℝ) ≤ √((12475 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.691539518443 : ℝ) ≤ √(12475 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12475) ≤ 0.124740050346 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037498748926 + 0.053058157190 * 1.772454 / (2 * (111.075537360842 : ℝ))) * (1 + 0.001210259966) +
        8 / (12475 * 111.691539518443) + 0.124740050346 := by gcongr
    _ ≤ (0.162713766074 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053058157190)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406156171) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283304221695) :
    parallelOracle 12475 0.011 xi bn cd ≤ 0.163722983619 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12475 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12475 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493209603 : ℝ) ≤ plow 12475 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.691539518443 : ℝ) ≤ √(12475 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283304221695 : ℝ) / (2 * 0.560493209603 * 111.691539518443)) * 0.162713766074 +
        0.283304221695 ^ 2 / (2 * 0.560493209603 * 111.691539518443) := by gcongr
    _ ≤ (0.163722983619 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053058157190) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406156171)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283304221695) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12475 12475 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493209603 : ℝ) ≤ plow 12475 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.691539518443 : ℝ) ≤ √(12475 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12475 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12475 Θ 1.22 ≤ 0.011872882277 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.691539518443 := by gcongr <;> linarith
      _ ≤ (0.011872882277 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12475 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12475 12475 0.011 ≤ 0.008558276657 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12475 12475 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12475 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12475 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12475 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12475 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163722983619 + 0.011872882277 + (0.008558276657 : ℝ) *
        (1 + 2 * (0.283304221695 + 0.011872882277) / (0.560493209603 * 111.691539518443))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12475]

end BstLean.Part269.N12475

/-! The original eight local profiles supply actual 12475 moment certificates. -/
namespace BstLean.Part269.N12475
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12475 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12475 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12475 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053058157190 ∧
    0 ≤ bN 12475 BstLean.Part154.csC (groupTheta g) ∧ bN 12475 BstLean.Part154.csC (groupTheta g) ≤ 0.001406156171 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12475 12475 0.011
      (momentAllowance 12475 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12475 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12475 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12475 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12475 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12475 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230343563379 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12475 0.011
      (momentAllowance 12475 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12475 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12475
/-! The actual computed-centre upper energy formula at 12475. -/
namespace BstLean.Part269.N12475
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12475

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12475
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12475)
open BstLean.Part268 (cell12475)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086176104984
  | 2 => 0.087132154036
  | 3 => 0.088088393375
  | 4 => 0.089046704938
  | 5 => 0.090009348233
  | 6 => 0.090979014186
  | 7 => 0.091958883655
  | 8 => 0.092952690581
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12475 12475 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12475 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12475

/-! Actual upper energy certificates on all 43 source endpoints at 12475. -/
namespace BstLean.Part269.N12475
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12475)
open BstLean.Part268 (cell12475)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12475 (gMinus 12475) (1 - (cell12475 i).lower) ≤ 1 ∧
    energyUpper 12475 (gMinus 12475) (BstLean.Part211.gPlus 12475)
      (finiteEnergy 12475 12475 0.011) (1 - (cell12475 i).lower) ≤
      (cell12475 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨10,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨11,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨12,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨13,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨14,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨15,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨16,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨17,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨18,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨19,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨20,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨21,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨22,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨23,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨24,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨25,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨26,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨27,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨28,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨29,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨30,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨31,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨32,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨33,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨34,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨35,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨36,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨37,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨38,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨39,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨40,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨41,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨42,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨43,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨44,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨45,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨46,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨47,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨48,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨49,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨50,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨51,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12475) (by norm_num)
        (q := 1 - (cell12475 ⟨52,by decide⟩).lower)
        (by norm_num [cell12475]) (by norm_num [cell12475])
      exact ⟨E.1,E.2.trans (by norm_num [cell12475])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12475

/-! Source-cell containment and simple scalar guards at 12475. -/
namespace BstLean.Part269.N12475
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12475)
open BstLean.Part268 (cell12475)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12475 ⟨10,by decide⟩).lower ∧ (cell12475 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12475 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12475 ⟨11,by decide⟩).lower ∧ (cell12475 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12475 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12475 ⟨12,by decide⟩).lower ∧ (cell12475 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12475 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12475 ⟨13,by decide⟩).lower ∧ (cell12475 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12475 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12475 ⟨14,by decide⟩).lower ∧ (cell12475 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12475 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12475 ⟨15,by decide⟩).lower ∧ (cell12475 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12475 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12475 ⟨16,by decide⟩).lower ∧ (cell12475 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12475 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12475 ⟨17,by decide⟩).lower ∧ (cell12475 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12475 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12475 ⟨18,by decide⟩).lower ∧ (cell12475 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12475 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12475 ⟨19,by decide⟩).lower ∧ (cell12475 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12475 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12475 ⟨20,by decide⟩).lower ∧ (cell12475 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12475 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12475 ⟨21,by decide⟩).lower ∧ (cell12475 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12475 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12475 ⟨22,by decide⟩).lower ∧ (cell12475 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12475 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12475 ⟨23,by decide⟩).lower ∧ (cell12475 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12475 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12475 ⟨24,by decide⟩).lower ∧ (cell12475 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12475 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12475 ⟨25,by decide⟩).lower ∧ (cell12475 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12475 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12475 ⟨26,by decide⟩).lower ∧ (cell12475 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12475 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12475 ⟨27,by decide⟩).lower ∧ (cell12475 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12475 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12475 ⟨28,by decide⟩).lower ∧ (cell12475 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12475 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12475 ⟨29,by decide⟩).lower ∧ (cell12475 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12475 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12475 ⟨30,by decide⟩).lower ∧ (cell12475 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12475 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12475 ⟨31,by decide⟩).lower ∧ (cell12475 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12475 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12475 ⟨32,by decide⟩).lower ∧ (cell12475 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12475 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12475 ⟨33,by decide⟩).lower ∧ (cell12475 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12475 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12475 ⟨34,by decide⟩).lower ∧ (cell12475 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12475 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12475 ⟨35,by decide⟩).lower ∧ (cell12475 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12475 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12475 ⟨36,by decide⟩).lower ∧ (cell12475 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12475 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12475 ⟨37,by decide⟩).lower ∧ (cell12475 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12475 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12475 ⟨38,by decide⟩).lower ∧ (cell12475 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12475 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12475 ⟨39,by decide⟩).lower ∧ (cell12475 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12475 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12475 ⟨40,by decide⟩).lower ∧ (cell12475 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12475 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12475 ⟨41,by decide⟩).lower ∧ (cell12475 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12475 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12475 ⟨42,by decide⟩).lower ∧ (cell12475 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12475 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12475 ⟨43,by decide⟩).lower ∧ (cell12475 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12475 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12475 ⟨44,by decide⟩).lower ∧ (cell12475 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12475 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12475 ⟨45,by decide⟩).lower ∧ (cell12475 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12475 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12475 ⟨46,by decide⟩).lower ∧ (cell12475 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12475 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12475 ⟨47,by decide⟩).lower ∧ (cell12475 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12475 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12475 ⟨48,by decide⟩).lower ∧ (cell12475 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12475 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12475 ⟨49,by decide⟩).lower ∧ (cell12475 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12475 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12475 ⟨50,by decide⟩).lower ∧ (cell12475 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12475 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12475 ⟨51,by decide⟩).lower ∧ (cell12475 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12475 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12475 ⟨52,by decide⟩).lower ∧ (cell12475 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12475 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12475 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12475 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12475,cell12475,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12475 i).lower ∧
    (cell12475 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12475 i).upper ≤ (0.532 : ℝ) ∧
    (cell12475 i).centre ≤ (0.1 : ℝ) ∧ (cell12475 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12475 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12475 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12475

/-! The local source numeric instances at 12475 have no network premises. -/
namespace BstLean.Part269.N12475
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12475)
open BstLean.Part268 (cell12475)

noncomputable def sourceNumerics12475 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12475 (cell12475 i)
      scalarRow12475.M scalarRow12475.H scalarRow12475.xi := by
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
    energy_allowance := scalarRow12475.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12475]
    centre_nonneg := (scalarRow12475.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12475])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12475
/-! Actual 12476 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12476
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12476 ≤ (1.036132098764 : ℝ) := by
  have hr : (111.696016043545 : ℝ) ≤ √(12476 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.696016043545 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12476 12476 (11 / 1000) ≤
    (0.008557933657 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12476) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.696016043545 : ℝ) ≤ √(12476 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12476)
  have hdiv : K / √(12476 : ℝ) ≤ K / 111.696016043545 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.696016043545 ≤ (0.008557933657 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12476.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12476 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12476 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12476 := gPlus_lower 12476
end BstLean.Part269.N12476

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12476
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036132098763 : ℝ) ≤ wn 12476 := by
  have hn : √(12476 : ℝ) ≤ 111.696016043546 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12476 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.696016043546 ≤ 2 / √(12476 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256483182 : ℝ) ≤ rhoBar 12476 BstLean.Part154.csC ∧
    rhoBar 12476 BstLean.Part154.csC ≤ 0.000256483579 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036132098763 : ℝ) / (1.295212 * 12476) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036132098764 : ℝ) / (1.29521 * 12476) := by gcongr
      _ ≤ (0.000256483579 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12476 BstLean.Part154.csC) ≤ 0.001026000100 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12476 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12476 BstLean.Part154.csC) (piBar (rhoBar 12476 BstLean.Part154.csC)) ≤ 0.000195904054 ∧
    cc1 (rhoBar 12476 BstLean.Part154.csC) (piBar (rhoBar 12476 BstLean.Part154.csC)) ≤ 0.000124655016 ∧
    cc2 (rhoBar 12476 BstLean.Part154.csC) ≤ 0.000072363150 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12476 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12476 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12476 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12476 BstLean.Part154.csC * nuR (rhoBar 12476 BstLean.Part154.csC)) ≤ 0.000512983604 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256483579 : ℝ) * 0.001026000100 := by gcongr
      _ ≤ (0.000512983604 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12476 BstLean.Part154.csC) * nuR (rhoBar 12476 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001026000100 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12476 BstLean.Part154.csC) * rhoBar 12476 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256483579 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256483579 / 2 + 0.399 * 0.001026000100 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195904054 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512983604 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124655016 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256483579 / 1.414213562 := by gcongr
      _ ≤ (0.000072363150 : ℝ) := by norm_num

end BstLean.Part269.N12476

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12476
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12476 BstLean.Part154.csC) (piBar (rhoBar 12476 BstLean.Part154.csC)) ≤ 1.65738E-7 := by
  have hr0 : 0 ≤ rhoBar 12476 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12476 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12476 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12476 BstLean.Part154.csC) (piBar (rhoBar 12476 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12476 BstLean.Part154.csC) (piBar (rhoBar 12476 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12476 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195904054 : ℝ) ^ 2 + 0.000124655016 ^ 2 + 3 * 0.000072363150 ^ 2 +
        2 * 0.797885 * 0.000195904054 * 0.000124655016 + 2 * 0.000195904054 * 0.000072363150 +
        4 * 0.797885 * 0.000124655016 * 0.000072363150 := by gcongr
    _ ≤ (1.65738E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12476 BstLean.Part154.csC Θ ≤ 0.002678171106 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12476 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12476 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12476 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12476 BstLean.Part154.csC) (piBar (rhoBar 12476 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12476 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036132098764 * 1.65738E-7 / (0.000256483182 : ℝ) := by gcongr
    _ ≤ 0.002678171106 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12476 BstLean.Part154.csC Θ ≤ 0.002972498680 + 0.000676729172 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12476 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12476 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12476 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036132098764 : ℝ) * ((2 * Θ * 0.000256483579 +
        (6863 / 10000) * 0.000256483579 * 12476 * 0.001026000100) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002972498680 + 0.000676729172 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12476 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12476 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12476 0.011 Θ ∧ gammaRatio 12476 0.011 Θ ≤ 0.000088172422 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12476 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036132098764 : ℝ) * 0.525 / ((1 - 0.011) * 12476) := by gcongr
      _ ≤ (0.000088172422 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12476 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12476 0.011 Θ) :=
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
    badAllowance 12476 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12476 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12476 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12476 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12476 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12476 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12476 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12476 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12476 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12476 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12476 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036132098764 : ℝ) * 12476 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12476 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003789837842 + 0.003354900278 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12476

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12476
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12476 BstLean.Part154.csC) (piBar (rhoBar 12476 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12476 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12476 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12476 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12476 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12476 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12476 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12476 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12476 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12476 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12476 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12476 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12476 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12476 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12476 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052958512556 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12476) ≤ 0.010691854763 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12476 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036132098764)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010691854763 + 2 * 0.737676 / 12476) := by gcongr
    _ ≤ (0.052958512556 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12476 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12476

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12476
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493256468 : ℝ) ≤ plow 12476 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12476) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057760488)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406039831) : eMP 12476 0.011 xi bn ≤ 0.001210161312 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12476 : ℝ) * (1 - 0.011))) ≤ 0.000598326094 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001406039831 / (12476 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598326094 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598326094 : ℝ) + 3.141593 * 0.053057760488 / (12476 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001210161312 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057760488)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406039831) : PiBarMP 12476 12 0.011 xi bn ≤ 0.162707189026 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12476 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037497197642 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.079989196974 : ℝ) ≤ √((12476 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.696016043545 : ℝ) ≤ √(12476 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12476) ≤ 0.124735051046 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037497197642 + 0.053057760488 * 1.772454 / (2 * (111.079989196974 : ℝ))) * (1 + 0.001210161312) +
        8 / (12476 * 111.696016043545) + 0.124735051046 := by gcongr
    _ ≤ (0.162707189026 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057760488)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406039831) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283301214824) :
    parallelOracle 12476 0.011 xi bn cd ≤ 0.163716333644 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12476 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12476 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493256468 : ℝ) ≤ plow 12476 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.696016043545 : ℝ) ≤ √(12476 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283301214824 : ℝ) / (2 * 0.560493256468 * 111.696016043545)) * 0.162707189026 +
        0.283301214824 ^ 2 / (2 * 0.560493256468 * 111.696016043545) := by gcongr
    _ ≤ (0.163716333644 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057760488) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001406039831)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283301214824) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12476 12476 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493256468 : ℝ) ≤ plow 12476 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.696016043545 : ℝ) ≤ √(12476 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12476 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12476 Θ 1.22 ≤ 0.011872406439 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.696016043545 := by gcongr <;> linarith
      _ ≤ (0.011872406439 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12476 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12476 12476 0.011 ≤ 0.008557933657 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12476 12476 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12476 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12476 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12476 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12476 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163716333644 + 0.011872406439 + (0.008557933657 : ℝ) *
        (1 + 2 * (0.283301214824 + 0.011872406439) / (0.560493256468 * 111.696016043545))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12476]

end BstLean.Part269.N12476

/-! The original eight local profiles supply actual 12476 moment certificates. -/
namespace BstLean.Part269.N12476
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12476 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12476 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12476 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053057760488 ∧
    0 ≤ bN 12476 BstLean.Part154.csC (groupTheta g) ∧ bN 12476 BstLean.Part154.csC (groupTheta g) ≤ 0.001406039831 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12476 12476 0.011
      (momentAllowance 12476 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12476 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12476 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12476 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12476 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12476 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230342702268 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12476 0.011
      (momentAllowance 12476 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12476 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12476
/-! The actual computed-centre upper energy formula at 12476. -/
namespace BstLean.Part269.N12476
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12476

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12476
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12476)
open BstLean.Part268 (cell12476)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086172914792
  | 2 => 0.087128898664
  | 3 => 0.088085062287
  | 4 => 0.089043285254
  | 5 => 0.090005824329
  | 6 => 0.090975367246
  | 7 => 0.091955091179
  | 8 => 0.092948725834
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12476 12476 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12476 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12476

/-! Actual upper energy certificates on all 43 source endpoints at 12476. -/
namespace BstLean.Part269.N12476
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12476)
open BstLean.Part268 (cell12476)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12476 (gMinus 12476) (1 - (cell12476 i).lower) ≤ 1 ∧
    energyUpper 12476 (gMinus 12476) (BstLean.Part211.gPlus 12476)
      (finiteEnergy 12476 12476 0.011) (1 - (cell12476 i).lower) ≤
      (cell12476 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨10,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨11,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨12,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨13,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨14,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨15,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨16,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨17,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨18,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨19,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨20,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨21,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨22,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨23,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨24,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨25,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨26,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨27,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨28,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨29,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨30,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨31,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨32,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨33,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨34,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨35,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨36,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨37,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨38,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨39,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨40,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨41,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨42,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨43,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨44,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨45,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨46,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨47,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨48,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨49,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨50,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨51,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12476) (by norm_num)
        (q := 1 - (cell12476 ⟨52,by decide⟩).lower)
        (by norm_num [cell12476]) (by norm_num [cell12476])
      exact ⟨E.1,E.2.trans (by norm_num [cell12476])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12476

/-! Source-cell containment and simple scalar guards at 12476. -/
namespace BstLean.Part269.N12476
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12476)
open BstLean.Part268 (cell12476)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12476 ⟨10,by decide⟩).lower ∧ (cell12476 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12476 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12476 ⟨11,by decide⟩).lower ∧ (cell12476 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12476 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12476 ⟨12,by decide⟩).lower ∧ (cell12476 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12476 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12476 ⟨13,by decide⟩).lower ∧ (cell12476 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12476 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12476 ⟨14,by decide⟩).lower ∧ (cell12476 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12476 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12476 ⟨15,by decide⟩).lower ∧ (cell12476 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12476 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12476 ⟨16,by decide⟩).lower ∧ (cell12476 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12476 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12476 ⟨17,by decide⟩).lower ∧ (cell12476 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12476 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12476 ⟨18,by decide⟩).lower ∧ (cell12476 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12476 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12476 ⟨19,by decide⟩).lower ∧ (cell12476 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12476 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12476 ⟨20,by decide⟩).lower ∧ (cell12476 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12476 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12476 ⟨21,by decide⟩).lower ∧ (cell12476 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12476 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12476 ⟨22,by decide⟩).lower ∧ (cell12476 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12476 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12476 ⟨23,by decide⟩).lower ∧ (cell12476 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12476 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12476 ⟨24,by decide⟩).lower ∧ (cell12476 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12476 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12476 ⟨25,by decide⟩).lower ∧ (cell12476 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12476 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12476 ⟨26,by decide⟩).lower ∧ (cell12476 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12476 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12476 ⟨27,by decide⟩).lower ∧ (cell12476 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12476 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12476 ⟨28,by decide⟩).lower ∧ (cell12476 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12476 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12476 ⟨29,by decide⟩).lower ∧ (cell12476 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12476 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12476 ⟨30,by decide⟩).lower ∧ (cell12476 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12476 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12476 ⟨31,by decide⟩).lower ∧ (cell12476 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12476 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12476 ⟨32,by decide⟩).lower ∧ (cell12476 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12476 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12476 ⟨33,by decide⟩).lower ∧ (cell12476 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12476 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12476 ⟨34,by decide⟩).lower ∧ (cell12476 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12476 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12476 ⟨35,by decide⟩).lower ∧ (cell12476 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12476 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12476 ⟨36,by decide⟩).lower ∧ (cell12476 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12476 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12476 ⟨37,by decide⟩).lower ∧ (cell12476 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12476 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12476 ⟨38,by decide⟩).lower ∧ (cell12476 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12476 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12476 ⟨39,by decide⟩).lower ∧ (cell12476 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12476 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12476 ⟨40,by decide⟩).lower ∧ (cell12476 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12476 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12476 ⟨41,by decide⟩).lower ∧ (cell12476 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12476 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12476 ⟨42,by decide⟩).lower ∧ (cell12476 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12476 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12476 ⟨43,by decide⟩).lower ∧ (cell12476 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12476 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12476 ⟨44,by decide⟩).lower ∧ (cell12476 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12476 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12476 ⟨45,by decide⟩).lower ∧ (cell12476 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12476 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12476 ⟨46,by decide⟩).lower ∧ (cell12476 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12476 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12476 ⟨47,by decide⟩).lower ∧ (cell12476 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12476 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12476 ⟨48,by decide⟩).lower ∧ (cell12476 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12476 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12476 ⟨49,by decide⟩).lower ∧ (cell12476 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12476 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12476 ⟨50,by decide⟩).lower ∧ (cell12476 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12476 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12476 ⟨51,by decide⟩).lower ∧ (cell12476 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12476 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12476 ⟨52,by decide⟩).lower ∧ (cell12476 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12476 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12476 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12476 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12476,cell12476,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12476 i).lower ∧
    (cell12476 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12476 i).upper ≤ (0.532 : ℝ) ∧
    (cell12476 i).centre ≤ (0.1 : ℝ) ∧ (cell12476 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12476 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12476 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12476

/-! The local source numeric instances at 12476 have no network premises. -/
namespace BstLean.Part269.N12476
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12476)
open BstLean.Part268 (cell12476)

noncomputable def sourceNumerics12476 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12476 (cell12476 i)
      scalarRow12476.M scalarRow12476.H scalarRow12476.xi := by
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
    energy_allowance := scalarRow12476.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12476]
    centre_nonneg := (scalarRow12476.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12476])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12476
/-! Actual 12477 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12477
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12477 ≤ (1.036130637939 : ℝ) := by
  have hr : (111.700492389245 : ℝ) ≤ √(12477 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.700492389245 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12477 12477 (11 / 1000) ≤
    (0.008557590700 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12477) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.700492389245 : ℝ) ≤ √(12477 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12477)
  have hdiv : K / √(12477 : ℝ) ≤ K / 111.700492389245 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.700492389245 ≤ (0.008557590700 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12477.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12477 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12477 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12477 := gPlus_lower 12477
end BstLean.Part269.N12477

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12477
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036130637938 : ℝ) ≤ wn 12477 := by
  have hn : √(12477 : ℝ) ≤ 111.700492389246 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12477 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.700492389246 ≤ 2 / √(12477 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256462264 : ℝ) ≤ rhoBar 12477 BstLean.Part154.csC ∧
    rhoBar 12477 BstLean.Part154.csC ≤ 0.000256462661 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036130637938 : ℝ) / (1.295212 * 12477) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036130637939 : ℝ) / (1.29521 * 12477) := by gcongr
      _ ≤ (0.000256462661 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12477 BstLean.Part154.csC) ≤ 0.001025916418 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12477 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12477 BstLean.Part154.csC) (piBar (rhoBar 12477 BstLean.Part154.csC)) ≤ 0.000195888076 ∧
    cc1 (rhoBar 12477 BstLean.Part154.csC) (piBar (rhoBar 12477 BstLean.Part154.csC)) ≤ 0.000124644850 ∧
    cc2 (rhoBar 12477 BstLean.Part154.csC) ≤ 0.000072357249 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12477 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12477 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12477 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12477 BstLean.Part154.csC * nuR (rhoBar 12477 BstLean.Part154.csC)) ≤ 0.000512941766 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256462661 : ℝ) * 0.001025916418 := by gcongr
      _ ≤ (0.000512941766 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12477 BstLean.Part154.csC) * nuR (rhoBar 12477 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001025916418 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12477 BstLean.Part154.csC) * rhoBar 12477 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256462661 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256462661 / 2 + 0.399 * 0.001025916418 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195888076 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512941766 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124644850 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256462661 / 1.414213562 := by gcongr
      _ ≤ (0.000072357249 : ℝ) := by norm_num

end BstLean.Part269.N12477

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12477
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12477 BstLean.Part154.csC) (piBar (rhoBar 12477 BstLean.Part154.csC)) ≤ 1.65711E-7 := by
  have hr0 : 0 ≤ rhoBar 12477 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12477 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12477 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12477 BstLean.Part154.csC) (piBar (rhoBar 12477 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12477 BstLean.Part154.csC) (piBar (rhoBar 12477 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12477 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195888076 : ℝ) ^ 2 + 0.000124644850 ^ 2 + 3 * 0.000072357249 ^ 2 +
        2 * 0.797885 * 0.000195888076 * 0.000124644850 + 2 * 0.000195888076 * 0.000072357249 +
        4 * 0.797885 * 0.000124644850 * 0.000072357249 := by gcongr
    _ ≤ (1.65711E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12477 BstLean.Part154.csC Θ ≤ 0.002677949442 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12477 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12477 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12477 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12477 BstLean.Part154.csC) (piBar (rhoBar 12477 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12477 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036130637939 * 1.65711E-7 / (0.000256462264 : ℝ) := by gcongr
    _ ≤ 0.002677949442 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12477 BstLean.Part154.csC Θ ≤ 0.002972247859 + 0.000676673026 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12477 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12477 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12477 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036130637939 : ℝ) * ((2 * Θ * 0.000256462661 +
        (6863 / 10000) * 0.000256462661 * 12477 * 0.001025916418) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002972247859 + 0.000676673026 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12477 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12477 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12477 0.011 Θ ∧ gammaRatio 12477 0.011 Θ ≤ 0.000088165231 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12477 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036130637939 : ℝ) * 0.525 / ((1 - 0.011) * 12477) := by gcongr
      _ ≤ (0.000088165231 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12477 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12477 0.011 Θ) :=
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
    badAllowance 12477 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12477 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12477 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12477 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12477 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12477 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12477 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12477 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12477 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12477 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12477 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036130637939 : ℝ) * 12477 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12477 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003789587021 + 0.003354622468 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12477

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12477
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12477 BstLean.Part154.csC) (piBar (rhoBar 12477 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12477 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12477 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12477 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12477 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12477 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12477 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12477 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12477 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12477 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12477 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12477 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12477 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12477 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12477 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052956367053 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12477) ≤ 0.010691426292 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12477 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036130637939)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010691426292 + 2 * 0.737676 / 12477) := by gcongr
    _ ≤ (0.052956367053 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12477 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12477

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12477
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493303326 : ℝ) ≤ plow 12477 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12477) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057363817)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405923458) : eMP 12477 0.011 xi bn ≤ 0.001210062652 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12477 : ℝ) * (1 - 0.011))) ≤ 0.000598277356 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001405923458 / (12477 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598277356 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598277356 : ℝ) + 3.141593 * 0.053057363817 / (12477 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001210062652 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057363817)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405923458) : PiBarMP 12477 12 0.011 xi bn ≤ 0.162700612076 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12477 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037495645854 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.084440854693 : ℝ) ≤ √((12477 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.700492389245 : ℝ) ≤ √(12477 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12477) ≤ 0.124730052346 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037495645854 + 0.053057363817 * 1.772454 / (2 * (111.084440854693 : ℝ))) * (1 + 0.001210062652) +
        8 / (12477 * 111.700492389245) + 0.124730052346 := by gcongr
    _ ≤ (0.162700612076 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057363817)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405923458) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283298208274) :
    parallelOracle 12477 0.011 xi bn cd ≤ 0.163709683777 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12477 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12477 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493303326 : ℝ) ≤ plow 12477 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.700492389245 : ℝ) ≤ √(12477 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283298208274 : ℝ) / (2 * 0.560493303326 * 111.700492389245)) * 0.162700612076 +
        0.283298208274 ^ 2 / (2 * 0.560493303326 * 111.700492389245) := by gcongr
    _ ≤ (0.163709683777 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053057363817) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405923458)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283298208274) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12477 12477 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493303326 : ℝ) ≤ plow 12477 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.700492389245 : ℝ) ≤ √(12477 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12477 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12477 Θ 1.22 ≤ 0.011871930658 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.700492389245 := by gcongr <;> linarith
      _ ≤ (0.011871930658 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12477 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12477 12477 0.011 ≤ 0.008557590700 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12477 12477 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12477 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12477 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12477 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12477 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163709683777 + 0.011871930658 + (0.008557590700 : ℝ) *
        (1 + 2 * (0.283298208274 + 0.011871930658) / (0.560493303326 * 111.700492389245))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12477]

end BstLean.Part269.N12477

/-! The original eight local profiles supply actual 12477 moment certificates. -/
namespace BstLean.Part269.N12477
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12477 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12477 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12477 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053057363817 ∧
    0 ≤ bN 12477 BstLean.Part154.csC (groupTheta g) ∧ bN 12477 BstLean.Part154.csC (groupTheta g) ≤ 0.001405923458 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12477 12477 0.011
      (momentAllowance 12477 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12477 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12477 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12477 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12477 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12477 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230341841221 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12477 0.011
      (momentAllowance 12477 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12477 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12477
/-! The actual computed-centre upper energy formula at 12477. -/
namespace BstLean.Part269.N12477
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12477

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12477
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12477)
open BstLean.Part268 (cell12477)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086169725969
  | 2 => 0.087125644720
  | 3 => 0.088081732700
  | 4 => 0.089039867162
  | 5 => 0.090002302127
  | 6 => 0.090971722143
  | 7 => 0.091951300700
  | 8 => 0.092944763277
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12477 12477 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12477 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12477

/-! Actual upper energy certificates on all 43 source endpoints at 12477. -/
namespace BstLean.Part269.N12477
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12477)
open BstLean.Part268 (cell12477)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12477 (gMinus 12477) (1 - (cell12477 i).lower) ≤ 1 ∧
    energyUpper 12477 (gMinus 12477) (BstLean.Part211.gPlus 12477)
      (finiteEnergy 12477 12477 0.011) (1 - (cell12477 i).lower) ≤
      (cell12477 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨10,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨11,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨12,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨13,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨14,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨15,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨16,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨17,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨18,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨19,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨20,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨21,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨22,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨23,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨24,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨25,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨26,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨27,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨28,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨29,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨30,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨31,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨32,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨33,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨34,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨35,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨36,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨37,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨38,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨39,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨40,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨41,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨42,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨43,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨44,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨45,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨46,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨47,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨48,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨49,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨50,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨51,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12477) (by norm_num)
        (q := 1 - (cell12477 ⟨52,by decide⟩).lower)
        (by norm_num [cell12477]) (by norm_num [cell12477])
      exact ⟨E.1,E.2.trans (by norm_num [cell12477])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12477

/-! Source-cell containment and simple scalar guards at 12477. -/
namespace BstLean.Part269.N12477
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12477)
open BstLean.Part268 (cell12477)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12477 ⟨10,by decide⟩).lower ∧ (cell12477 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12477 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12477 ⟨11,by decide⟩).lower ∧ (cell12477 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12477 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12477 ⟨12,by decide⟩).lower ∧ (cell12477 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12477 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12477 ⟨13,by decide⟩).lower ∧ (cell12477 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12477 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12477 ⟨14,by decide⟩).lower ∧ (cell12477 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12477 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12477 ⟨15,by decide⟩).lower ∧ (cell12477 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12477 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12477 ⟨16,by decide⟩).lower ∧ (cell12477 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12477 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12477 ⟨17,by decide⟩).lower ∧ (cell12477 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12477 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12477 ⟨18,by decide⟩).lower ∧ (cell12477 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12477 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12477 ⟨19,by decide⟩).lower ∧ (cell12477 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12477 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12477 ⟨20,by decide⟩).lower ∧ (cell12477 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12477 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12477 ⟨21,by decide⟩).lower ∧ (cell12477 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12477 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12477 ⟨22,by decide⟩).lower ∧ (cell12477 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12477 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12477 ⟨23,by decide⟩).lower ∧ (cell12477 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12477 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12477 ⟨24,by decide⟩).lower ∧ (cell12477 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12477 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12477 ⟨25,by decide⟩).lower ∧ (cell12477 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12477 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12477 ⟨26,by decide⟩).lower ∧ (cell12477 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12477 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12477 ⟨27,by decide⟩).lower ∧ (cell12477 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12477 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12477 ⟨28,by decide⟩).lower ∧ (cell12477 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12477 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12477 ⟨29,by decide⟩).lower ∧ (cell12477 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12477 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12477 ⟨30,by decide⟩).lower ∧ (cell12477 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12477 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12477 ⟨31,by decide⟩).lower ∧ (cell12477 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12477 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12477 ⟨32,by decide⟩).lower ∧ (cell12477 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12477 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12477 ⟨33,by decide⟩).lower ∧ (cell12477 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12477 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12477 ⟨34,by decide⟩).lower ∧ (cell12477 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12477 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12477 ⟨35,by decide⟩).lower ∧ (cell12477 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12477 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12477 ⟨36,by decide⟩).lower ∧ (cell12477 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12477 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12477 ⟨37,by decide⟩).lower ∧ (cell12477 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12477 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12477 ⟨38,by decide⟩).lower ∧ (cell12477 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12477 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12477 ⟨39,by decide⟩).lower ∧ (cell12477 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12477 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12477 ⟨40,by decide⟩).lower ∧ (cell12477 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12477 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12477 ⟨41,by decide⟩).lower ∧ (cell12477 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12477 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12477 ⟨42,by decide⟩).lower ∧ (cell12477 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12477 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12477 ⟨43,by decide⟩).lower ∧ (cell12477 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12477 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12477 ⟨44,by decide⟩).lower ∧ (cell12477 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12477 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12477 ⟨45,by decide⟩).lower ∧ (cell12477 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12477 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12477 ⟨46,by decide⟩).lower ∧ (cell12477 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12477 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12477 ⟨47,by decide⟩).lower ∧ (cell12477 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12477 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12477 ⟨48,by decide⟩).lower ∧ (cell12477 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12477 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12477 ⟨49,by decide⟩).lower ∧ (cell12477 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12477 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12477 ⟨50,by decide⟩).lower ∧ (cell12477 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12477 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12477 ⟨51,by decide⟩).lower ∧ (cell12477 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12477 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12477 ⟨52,by decide⟩).lower ∧ (cell12477 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12477 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12477 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12477 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12477,cell12477,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12477 i).lower ∧
    (cell12477 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12477 i).upper ≤ (0.532 : ℝ) ∧
    (cell12477 i).centre ≤ (0.1 : ℝ) ∧ (cell12477 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12477 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12477 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12477

/-! The local source numeric instances at 12477 have no network premises. -/
namespace BstLean.Part269.N12477
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12477)
open BstLean.Part268 (cell12477)

noncomputable def sourceNumerics12477 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12477 (cell12477 i)
      scalarRow12477.M scalarRow12477.H scalarRow12477.xi := by
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
    energy_allowance := scalarRow12477.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12477]
    centre_nonneg := (scalarRow12477.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12477])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12477
/-! Actual 12478 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12478
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12478 ≤ (1.036129177290 : ℝ) := by
  have hr : (111.704968555566 : ℝ) ≤ √(12478 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.704968555566 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12478 12478 (11 / 1000) ≤
    (0.008557247783 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12478) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.704968555566 : ℝ) ≤ √(12478 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12478)
  have hdiv : K / √(12478 : ℝ) ≤ K / 111.704968555566 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.704968555566 ≤ (0.008557247783 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12478.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12478 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12478 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12478 := gPlus_lower 12478
end BstLean.Part269.N12478

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12478
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036129177289 : ℝ) ≤ wn 12478 := by
  have hn : √(12478 : ℝ) ≤ 111.704968555567 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12478 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.704968555567 ≤ 2 / √(12478 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256441349 : ℝ) ≤ rhoBar 12478 BstLean.Part154.csC ∧
    rhoBar 12478 BstLean.Part154.csC ≤ 0.000256441746 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036129177289 : ℝ) / (1.295212 * 12478) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036129177290 : ℝ) / (1.29521 * 12478) := by gcongr
      _ ≤ (0.000256441746 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12478 BstLean.Part154.csC) ≤ 0.001025832747 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12478 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12478 BstLean.Part154.csC) (piBar (rhoBar 12478 BstLean.Part154.csC)) ≤ 0.000195872101 ∧
    cc1 (rhoBar 12478 BstLean.Part154.csC) (piBar (rhoBar 12478 BstLean.Part154.csC)) ≤ 0.000124634684 ∧
    cc2 (rhoBar 12478 BstLean.Part154.csC) ≤ 0.000072351348 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12478 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12478 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12478 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12478 BstLean.Part154.csC * nuR (rhoBar 12478 BstLean.Part154.csC)) ≤ 0.000512899933 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256441746 : ℝ) * 0.001025832747 := by gcongr
      _ ≤ (0.000512899933 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12478 BstLean.Part154.csC) * nuR (rhoBar 12478 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001025832747 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12478 BstLean.Part154.csC) * rhoBar 12478 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256441746 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256441746 / 2 + 0.399 * 0.001025832747 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195872101 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512899933 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124634684 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256441746 / 1.414213562 := by gcongr
      _ ≤ (0.000072351348 : ℝ) := by norm_num

end BstLean.Part269.N12478

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12478
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12478 BstLean.Part154.csC) (piBar (rhoBar 12478 BstLean.Part154.csC)) ≤ 1.65684E-7 := by
  have hr0 : 0 ≤ rhoBar 12478 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12478 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12478 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12478 BstLean.Part154.csC) (piBar (rhoBar 12478 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12478 BstLean.Part154.csC) (piBar (rhoBar 12478 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12478 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195872101 : ℝ) ^ 2 + 0.000124634684 ^ 2 + 3 * 0.000072351348 ^ 2 +
        2 * 0.797885 * 0.000195872101 * 0.000124634684 + 2 * 0.000195872101 * 0.000072351348 +
        4 * 0.797885 * 0.000124634684 * 0.000072351348 := by gcongr
    _ ≤ (1.65684E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12478 BstLean.Part154.csC Θ ≤ 0.002677727711 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12478 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12478 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12478 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12478 BstLean.Part154.csC) (piBar (rhoBar 12478 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12478 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036129177290 * 1.65684E-7 / (0.000256441349 : ℝ) := by gcongr
    _ ≤ 0.002677727711 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12478 BstLean.Part154.csC Θ ≤ 0.002971997068 + 0.000676616889 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12478 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12478 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12478 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036129177290 : ℝ) * ((2 * Θ * 0.000256441746 +
        (6863 / 10000) * 0.000256441746 * 12478 * 0.001025832747) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002971997068 + 0.000676616889 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12478 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12478 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12478 0.011 Θ ∧ gammaRatio 12478 0.011 Θ ≤ 0.000088158041 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12478 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036129177290 : ℝ) * 0.525 / ((1 - 0.011) * 12478) := by gcongr
      _ ≤ (0.000088158041 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12478 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12478 0.011 Θ) :=
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
    badAllowance 12478 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12478 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12478 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12478 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12478 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12478 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12478 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12478 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12478 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12478 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12478 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036129177290 : ℝ) * 12478 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12478 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003789336230 + 0.003354344600 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12478

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12478
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12478 BstLean.Part154.csC) (piBar (rhoBar 12478 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12478 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12478 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12478 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12478 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12478 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12478 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12478 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12478 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12478 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12478 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12478 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12478 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12478 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12478 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052954221808 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12478) ≤ 0.010690997872 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12478 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036129177290)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010690997872 + 2 * 0.737676 / 12478) := by gcongr
    _ ≤ (0.052954221808 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12478 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12478

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12478
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493350176 : ℝ) ≤ plow 12478 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12478) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053056967145)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405807049) : eMP 12478 0.011 xi bn ≤ 0.001209963987 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12478 : ℝ) * (1 - 0.011))) ≤ 0.000598228615 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001405807049 / (12478 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598228615 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598228615 : ℝ) + 3.141593 * 0.053056967145 / (12478 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001209963987 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053056967145)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405807049) : PiBarMP 12478 12 0.011 xi bn ≤ 0.162694035185 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12478 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037494093522 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.088892334022 : ℝ) ≤ √((12478 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.704968555566 : ℝ) ≤ √(12478 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12478) ≤ 0.124725054247 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037494093522 + 0.053056967145 * 1.772454 / (2 * (111.088892334022 : ℝ))) * (1 + 0.001209963987) +
        8 / (12478 * 111.704968555566) + 0.124725054247 := by gcongr
    _ ≤ (0.162694035185 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053056967145)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405807049) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283295201977) :
    parallelOracle 12478 0.011 xi bn cd ≤ 0.163703033978 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12478 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12478 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493350176 : ℝ) ≤ plow 12478 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.704968555566 : ℝ) ≤ √(12478 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283295201977 : ℝ) / (2 * 0.560493350176 * 111.704968555566)) * 0.162694035185 +
        0.283295201977 ^ 2 / (2 * 0.560493350176 * 111.704968555566) := by gcongr
    _ ≤ (0.163703033978 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053056967145) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405807049)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283295201977) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12478 12478 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493350176 : ℝ) ≤ plow 12478 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.704968555566 : ℝ) ≤ √(12478 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12478 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12478 Θ 1.22 ≤ 0.011871454934 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.704968555566 := by gcongr <;> linarith
      _ ≤ (0.011871454934 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12478 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12478 12478 0.011 ≤ 0.008557247783 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12478 12478 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12478 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12478 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12478 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12478 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163703033978 + 0.011871454934 + (0.008557247783 : ℝ) *
        (1 + 2 * (0.283295201977 + 0.011871454934) / (0.560493350176 * 111.704968555566))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12478]

end BstLean.Part269.N12478

/-! The original eight local profiles supply actual 12478 moment certificates. -/
namespace BstLean.Part269.N12478
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12478 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12478 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12478 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053056967145 ∧
    0 ≤ bN 12478 BstLean.Part154.csC (groupTheta g) ∧ bN 12478 BstLean.Part154.csC (groupTheta g) ≤ 0.001405807049 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12478 12478 0.011
      (momentAllowance 12478 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12478 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12478 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12478 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12478 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12478 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230340980169 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12478 0.011
      (momentAllowance 12478 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12478 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12478
/-! The actual computed-centre upper energy formula at 12478. -/
namespace BstLean.Part269.N12478
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12478

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12478
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12478)
open BstLean.Part268 (cell12478)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086166538514
  | 2 => 0.087122392204
  | 3 => 0.088078404615
  | 4 => 0.089036450661
  | 5 => 0.089998781626
  | 6 => 0.090968078873
  | 7 => 0.091947512215
  | 8 => 0.092940802906
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12478 12478 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12478 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12478

/-! Actual upper energy certificates on all 43 source endpoints at 12478. -/
namespace BstLean.Part269.N12478
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12478)
open BstLean.Part268 (cell12478)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12478 (gMinus 12478) (1 - (cell12478 i).lower) ≤ 1 ∧
    energyUpper 12478 (gMinus 12478) (BstLean.Part211.gPlus 12478)
      (finiteEnergy 12478 12478 0.011) (1 - (cell12478 i).lower) ≤
      (cell12478 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨10,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨11,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨12,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨13,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨14,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨15,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨16,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨17,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨18,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨19,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨20,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨21,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨22,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨23,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨24,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨25,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨26,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨27,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨28,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨29,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨30,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨31,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨32,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨33,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨34,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨35,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨36,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨37,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨38,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨39,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨40,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨41,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨42,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨43,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨44,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨45,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨46,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨47,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨48,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨49,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨50,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨51,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12478) (by norm_num)
        (q := 1 - (cell12478 ⟨52,by decide⟩).lower)
        (by norm_num [cell12478]) (by norm_num [cell12478])
      exact ⟨E.1,E.2.trans (by norm_num [cell12478])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12478

/-! Source-cell containment and simple scalar guards at 12478. -/
namespace BstLean.Part269.N12478
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12478)
open BstLean.Part268 (cell12478)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12478 ⟨10,by decide⟩).lower ∧ (cell12478 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12478 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12478 ⟨11,by decide⟩).lower ∧ (cell12478 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12478 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12478 ⟨12,by decide⟩).lower ∧ (cell12478 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12478 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12478 ⟨13,by decide⟩).lower ∧ (cell12478 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12478 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12478 ⟨14,by decide⟩).lower ∧ (cell12478 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12478 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12478 ⟨15,by decide⟩).lower ∧ (cell12478 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12478 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12478 ⟨16,by decide⟩).lower ∧ (cell12478 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12478 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12478 ⟨17,by decide⟩).lower ∧ (cell12478 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12478 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12478 ⟨18,by decide⟩).lower ∧ (cell12478 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12478 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12478 ⟨19,by decide⟩).lower ∧ (cell12478 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12478 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12478 ⟨20,by decide⟩).lower ∧ (cell12478 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12478 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12478 ⟨21,by decide⟩).lower ∧ (cell12478 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12478 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12478 ⟨22,by decide⟩).lower ∧ (cell12478 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12478 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12478 ⟨23,by decide⟩).lower ∧ (cell12478 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12478 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12478 ⟨24,by decide⟩).lower ∧ (cell12478 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12478 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12478 ⟨25,by decide⟩).lower ∧ (cell12478 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12478 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12478 ⟨26,by decide⟩).lower ∧ (cell12478 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12478 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12478 ⟨27,by decide⟩).lower ∧ (cell12478 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12478 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12478 ⟨28,by decide⟩).lower ∧ (cell12478 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12478 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12478 ⟨29,by decide⟩).lower ∧ (cell12478 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12478 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12478 ⟨30,by decide⟩).lower ∧ (cell12478 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12478 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12478 ⟨31,by decide⟩).lower ∧ (cell12478 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12478 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12478 ⟨32,by decide⟩).lower ∧ (cell12478 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12478 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12478 ⟨33,by decide⟩).lower ∧ (cell12478 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12478 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12478 ⟨34,by decide⟩).lower ∧ (cell12478 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12478 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12478 ⟨35,by decide⟩).lower ∧ (cell12478 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12478 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12478 ⟨36,by decide⟩).lower ∧ (cell12478 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12478 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12478 ⟨37,by decide⟩).lower ∧ (cell12478 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12478 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12478 ⟨38,by decide⟩).lower ∧ (cell12478 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12478 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12478 ⟨39,by decide⟩).lower ∧ (cell12478 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12478 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12478 ⟨40,by decide⟩).lower ∧ (cell12478 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12478 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12478 ⟨41,by decide⟩).lower ∧ (cell12478 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12478 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12478 ⟨42,by decide⟩).lower ∧ (cell12478 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12478 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12478 ⟨43,by decide⟩).lower ∧ (cell12478 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12478 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12478 ⟨44,by decide⟩).lower ∧ (cell12478 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12478 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12478 ⟨45,by decide⟩).lower ∧ (cell12478 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12478 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12478 ⟨46,by decide⟩).lower ∧ (cell12478 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12478 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12478 ⟨47,by decide⟩).lower ∧ (cell12478 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12478 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12478 ⟨48,by decide⟩).lower ∧ (cell12478 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12478 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12478 ⟨49,by decide⟩).lower ∧ (cell12478 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12478 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12478 ⟨50,by decide⟩).lower ∧ (cell12478 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12478 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12478 ⟨51,by decide⟩).lower ∧ (cell12478 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12478 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12478 ⟨52,by decide⟩).lower ∧ (cell12478 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12478 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12478 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12478 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12478,cell12478,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12478 i).lower ∧
    (cell12478 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12478 i).upper ≤ (0.532 : ℝ) ∧
    (cell12478 i).centre ≤ (0.1 : ℝ) ∧ (cell12478 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12478 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12478 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12478

/-! The local source numeric instances at 12478 have no network premises. -/
namespace BstLean.Part269.N12478
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12478)
open BstLean.Part268 (cell12478)

noncomputable def sourceNumerics12478 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12478 (cell12478 i)
      scalarRow12478.M scalarRow12478.H scalarRow12478.xi := by
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
    energy_allowance := scalarRow12478.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12478]
    centre_nonneg := (scalarRow12478.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12478])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12478
/-! Actual 12479 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12479
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12479 ≤ (1.036127716818 : ℝ) := by
  have hr : (111.709444542527 : ℝ) ≤ √(12479 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.709444542527 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12479 12479 (11 / 1000) ≤
    (0.008556904907 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12479) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.709444542527 : ℝ) ≤ √(12479 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12479)
  have hdiv : K / √(12479 : ℝ) ≤ K / 111.709444542527 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.709444542527 ≤ (0.008556904907 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12479.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12479 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12479 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12479 := gPlus_lower 12479
end BstLean.Part269.N12479

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12479
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036127716817 : ℝ) ≤ wn 12479 := by
  have hn : √(12479 : ℝ) ≤ 111.709444542528 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12479 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.709444542528 ≤ 2 / √(12479 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256420438 : ℝ) ≤ rhoBar 12479 BstLean.Part154.csC ∧
    rhoBar 12479 BstLean.Part154.csC ≤ 0.000256420835 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036127716817 : ℝ) / (1.295212 * 12479) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036127716818 : ℝ) / (1.29521 * 12479) := by gcongr
      _ ≤ (0.000256420835 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12479 BstLean.Part154.csC) ≤ 0.001025749092 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12479 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12479 BstLean.Part154.csC) (piBar (rhoBar 12479 BstLean.Part154.csC)) ≤ 0.000195856128 ∧
    cc1 (rhoBar 12479 BstLean.Part154.csC) (piBar (rhoBar 12479 BstLean.Part154.csC)) ≤ 0.000124624521 ∧
    cc2 (rhoBar 12479 BstLean.Part154.csC) ≤ 0.000072345448 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12479 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12479 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12479 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12479 BstLean.Part154.csC * nuR (rhoBar 12479 BstLean.Part154.csC)) ≤ 0.000512858108 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256420835 : ℝ) * 0.001025749092 := by gcongr
      _ ≤ (0.000512858108 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12479 BstLean.Part154.csC) * nuR (rhoBar 12479 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001025749092 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12479 BstLean.Part154.csC) * rhoBar 12479 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256420835 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256420835 / 2 + 0.399 * 0.001025749092 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195856128 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512858108 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124624521 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256420835 / 1.414213562 := by gcongr
      _ ≤ (0.000072345448 : ℝ) := by norm_num

end BstLean.Part269.N12479

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12479
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12479 BstLean.Part154.csC) (piBar (rhoBar 12479 BstLean.Part154.csC)) ≤ 1.65657E-7 := by
  have hr0 : 0 ≤ rhoBar 12479 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12479 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12479 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12479 BstLean.Part154.csC) (piBar (rhoBar 12479 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12479 BstLean.Part154.csC) (piBar (rhoBar 12479 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12479 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195856128 : ℝ) ^ 2 + 0.000124624521 ^ 2 + 3 * 0.000072345448 ^ 2 +
        2 * 0.797885 * 0.000195856128 * 0.000124624521 + 2 * 0.000195856128 * 0.000072345448 +
        4 * 0.797885 * 0.000124624521 * 0.000072345448 := by gcongr
    _ ≤ (1.65657E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12479 BstLean.Part154.csC Θ ≤ 0.002677505905 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12479 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12479 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12479 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12479 BstLean.Part154.csC) (piBar (rhoBar 12479 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12479 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036127716818 * 1.65657E-7 / (0.000256420438 : ℝ) := by gcongr
    _ ≤ 0.002677505905 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12479 BstLean.Part154.csC Θ ≤ 0.002971746332 + 0.000676560762 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12479 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12479 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12479 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036127716818 : ℝ) * ((2 * Θ * 0.000256420835 +
        (6863 / 10000) * 0.000256420835 * 12479 * 0.001025749092) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002971746332 + 0.000676560762 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12479 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12479 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12479 0.011 Θ ∧ gammaRatio 12479 0.011 Θ ≤ 0.000088150852 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12479 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036127716818 : ℝ) * 0.525 / ((1 - 0.011) * 12479) := by gcongr
      _ ≤ (0.000088150852 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12479 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12479 0.011 Θ) :=
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
    badAllowance 12479 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12479 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12479 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12479 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12479 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12479 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12479 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12479 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12479 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12479 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12479 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036127716818 : ℝ) * 12479 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12479 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003789085494 + 0.003354066667 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12479

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12479
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12479 BstLean.Part154.csC) (piBar (rhoBar 12479 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12479 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12479 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12479 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12479 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12479 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12479 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12479 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12479 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12479 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12479 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12479 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12479 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12479 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12479 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052952076825 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12479) ≤ 0.010690569504 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12479 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036127716818)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010690569504 + 2 * 0.737676 / 12479) := by gcongr
    _ ≤ (0.052952076825 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12479 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12479

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12479
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493397018 : ℝ) ≤ plow 12479 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12479) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053056570495)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405690601) : eMP 12479 0.011 xi bn ≤ 0.001209865312 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12479 : ℝ) * (1 - 0.011))) ≤ 0.000598179869 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001405690601 / (12479 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598179869 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598179869 : ℝ) + 3.141593 * 0.053056570495 / (12479 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001209865312 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053056570495)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405690601) : PiBarMP 12479 12 0.011 xi bn ≤ 0.162687458312 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12479 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037492540605 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.093343634981 : ℝ) ≤ √((12479 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.709444542527 : ℝ) ≤ √(12479 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12479) ≤ 0.124720056750 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037492540605 + 0.053056570495 * 1.772454 / (2 * (111.093343634981 : ℝ))) * (1 + 0.001209865312) +
        8 / (12479 * 111.709444542527) + 0.124720056750 := by gcongr
    _ ≤ (0.162687458312 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053056570495)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405690601) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283292195986) :
    parallelOracle 12479 0.011 xi bn cd ≤ 0.163696384208 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12479 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12479 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493397018 : ℝ) ≤ plow 12479 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.709444542527 : ℝ) ≤ √(12479 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283292195986 : ℝ) / (2 * 0.560493397018 * 111.709444542527)) * 0.162687458312 +
        0.283292195986 ^ 2 / (2 * 0.560493397018 * 111.709444542527) := by gcongr
    _ ≤ (0.163696384208 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053056570495) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405690601)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283292195986) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12479 12479 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493397018 : ℝ) ≤ plow 12479 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.709444542527 : ℝ) ≤ √(12479 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12479 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12479 Θ 1.22 ≤ 0.011870979267 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.709444542527 := by gcongr <;> linarith
      _ ≤ (0.011870979267 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12479 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12479 12479 0.011 ≤ 0.008556904907 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12479 12479 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12479 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12479 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12479 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12479 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163696384208 + 0.011870979267 + (0.008556904907 : ℝ) *
        (1 + 2 * (0.283292195986 + 0.011870979267) / (0.560493397018 * 111.709444542527))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12479]

end BstLean.Part269.N12479

/-! The original eight local profiles supply actual 12479 moment certificates. -/
namespace BstLean.Part269.N12479
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12479 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12479 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12479 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053056570495 ∧
    0 ≤ bN 12479 BstLean.Part154.csC (groupTheta g) ∧ bN 12479 BstLean.Part154.csC (groupTheta g) ≤ 0.001405690601 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12479 12479 0.011
      (momentAllowance 12479 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12479 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12479 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12479 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12479 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12479 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230340119161 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12479 0.011
      (momentAllowance 12479 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12479 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12479
/-! The actual computed-centre upper energy formula at 12479. -/
namespace BstLean.Part269.N12479
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12479

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12479
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12479)
open BstLean.Part268 (cell12479)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086163352425
  | 2 => 0.087119141113
  | 3 => 0.088075078029
  | 4 => 0.089033035749
  | 5 => 0.089995262823
  | 6 => 0.090964437436
  | 7 => 0.091943725723
  | 8 => 0.092936844721
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12479 12479 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12479 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12479

/-! Actual upper energy certificates on all 43 source endpoints at 12479. -/
namespace BstLean.Part269.N12479
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12479)
open BstLean.Part268 (cell12479)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12479 (gMinus 12479) (1 - (cell12479 i).lower) ≤ 1 ∧
    energyUpper 12479 (gMinus 12479) (BstLean.Part211.gPlus 12479)
      (finiteEnergy 12479 12479 0.011) (1 - (cell12479 i).lower) ≤
      (cell12479 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨10,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨11,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨12,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨13,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨14,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨15,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨16,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨17,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨18,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨19,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨20,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨21,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨22,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨23,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨24,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨25,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨26,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨27,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨28,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨29,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨30,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨31,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨32,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨33,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨34,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨35,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨36,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨37,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨38,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨39,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨40,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨41,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨42,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨43,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨44,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨45,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨46,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨47,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨48,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨49,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨50,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨51,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12479) (by norm_num)
        (q := 1 - (cell12479 ⟨52,by decide⟩).lower)
        (by norm_num [cell12479]) (by norm_num [cell12479])
      exact ⟨E.1,E.2.trans (by norm_num [cell12479])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12479

/-! Source-cell containment and simple scalar guards at 12479. -/
namespace BstLean.Part269.N12479
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12479)
open BstLean.Part268 (cell12479)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12479 ⟨10,by decide⟩).lower ∧ (cell12479 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12479 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12479 ⟨11,by decide⟩).lower ∧ (cell12479 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12479 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12479 ⟨12,by decide⟩).lower ∧ (cell12479 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12479 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12479 ⟨13,by decide⟩).lower ∧ (cell12479 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12479 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12479 ⟨14,by decide⟩).lower ∧ (cell12479 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12479 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12479 ⟨15,by decide⟩).lower ∧ (cell12479 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12479 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12479 ⟨16,by decide⟩).lower ∧ (cell12479 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12479 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12479 ⟨17,by decide⟩).lower ∧ (cell12479 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12479 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12479 ⟨18,by decide⟩).lower ∧ (cell12479 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12479 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12479 ⟨19,by decide⟩).lower ∧ (cell12479 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12479 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12479 ⟨20,by decide⟩).lower ∧ (cell12479 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12479 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12479 ⟨21,by decide⟩).lower ∧ (cell12479 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12479 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12479 ⟨22,by decide⟩).lower ∧ (cell12479 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12479 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12479 ⟨23,by decide⟩).lower ∧ (cell12479 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12479 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12479 ⟨24,by decide⟩).lower ∧ (cell12479 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12479 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12479 ⟨25,by decide⟩).lower ∧ (cell12479 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12479 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12479 ⟨26,by decide⟩).lower ∧ (cell12479 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12479 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12479 ⟨27,by decide⟩).lower ∧ (cell12479 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12479 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12479 ⟨28,by decide⟩).lower ∧ (cell12479 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12479 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12479 ⟨29,by decide⟩).lower ∧ (cell12479 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12479 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12479 ⟨30,by decide⟩).lower ∧ (cell12479 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12479 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12479 ⟨31,by decide⟩).lower ∧ (cell12479 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12479 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12479 ⟨32,by decide⟩).lower ∧ (cell12479 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12479 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12479 ⟨33,by decide⟩).lower ∧ (cell12479 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12479 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12479 ⟨34,by decide⟩).lower ∧ (cell12479 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12479 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12479 ⟨35,by decide⟩).lower ∧ (cell12479 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12479 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12479 ⟨36,by decide⟩).lower ∧ (cell12479 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12479 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12479 ⟨37,by decide⟩).lower ∧ (cell12479 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12479 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12479 ⟨38,by decide⟩).lower ∧ (cell12479 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12479 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12479 ⟨39,by decide⟩).lower ∧ (cell12479 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12479 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12479 ⟨40,by decide⟩).lower ∧ (cell12479 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12479 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12479 ⟨41,by decide⟩).lower ∧ (cell12479 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12479 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12479 ⟨42,by decide⟩).lower ∧ (cell12479 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12479 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12479 ⟨43,by decide⟩).lower ∧ (cell12479 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12479 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12479 ⟨44,by decide⟩).lower ∧ (cell12479 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12479 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12479 ⟨45,by decide⟩).lower ∧ (cell12479 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12479 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12479 ⟨46,by decide⟩).lower ∧ (cell12479 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12479 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12479 ⟨47,by decide⟩).lower ∧ (cell12479 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12479 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12479 ⟨48,by decide⟩).lower ∧ (cell12479 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12479 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12479 ⟨49,by decide⟩).lower ∧ (cell12479 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12479 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12479 ⟨50,by decide⟩).lower ∧ (cell12479 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12479 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12479 ⟨51,by decide⟩).lower ∧ (cell12479 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12479 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12479 ⟨52,by decide⟩).lower ∧ (cell12479 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12479 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12479 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12479 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12479,cell12479,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12479 i).lower ∧
    (cell12479 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12479 i).upper ≤ (0.532 : ℝ) ∧
    (cell12479 i).centre ≤ (0.1 : ℝ) ∧ (cell12479 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12479 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12479 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12479

/-! The local source numeric instances at 12479 have no network premises. -/
namespace BstLean.Part269.N12479
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12479)
open BstLean.Part268 (cell12479)

noncomputable def sourceNumerics12479 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12479 (cell12479 i)
      scalarRow12479.M scalarRow12479.H scalarRow12479.xi := by
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
    energy_allowance := scalarRow12479.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12479]
    centre_nonneg := (scalarRow12479.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12479])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12479
/-! Actual 12480 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12480
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12480 ≤ (1.036126256523 : ℝ) := by
  have hr : (111.713920350151 : ℝ) ≤ √(12480 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.713920350151 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12480 12480 (11 / 1000) ≤
    (0.008556562073 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12480) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.713920350151 : ℝ) ≤ √(12480 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12480)
  have hdiv : K / √(12480 : ℝ) ≤ K / 111.713920350151 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.713920350151 ≤ (0.008556562073 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12480.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12480 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12480 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12480 := gPlus_lower 12480
end BstLean.Part269.N12480

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12480
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036126256522 : ℝ) ≤ wn 12480 := by
  have hn : √(12480 : ℝ) ≤ 111.713920350152 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12480 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.713920350152 ≤ 2 / √(12480 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256399530 : ℝ) ≤ rhoBar 12480 BstLean.Part154.csC ∧
    rhoBar 12480 BstLean.Part154.csC ≤ 0.000256399927 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036126256522 : ℝ) / (1.295212 * 12480) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036126256523 : ℝ) / (1.29521 * 12480) := by gcongr
      _ ≤ (0.000256399927 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12480 BstLean.Part154.csC) ≤ 0.001025665449 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12480 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12480 BstLean.Part154.csC) (piBar (rhoBar 12480 BstLean.Part154.csC)) ≤ 0.000195840157 ∧
    cc1 (rhoBar 12480 BstLean.Part154.csC) (piBar (rhoBar 12480 BstLean.Part154.csC)) ≤ 0.000124614359 ∧
    cc2 (rhoBar 12480 BstLean.Part154.csC) ≤ 0.000072339549 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12480 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12480 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12480 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12480 BstLean.Part154.csC * nuR (rhoBar 12480 BstLean.Part154.csC)) ≤ 0.000512816289 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256399927 : ℝ) * 0.001025665449 := by gcongr
      _ ≤ (0.000512816289 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12480 BstLean.Part154.csC) * nuR (rhoBar 12480 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001025665449 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12480 BstLean.Part154.csC) * rhoBar 12480 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256399927 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256399927 / 2 + 0.399 * 0.001025665449 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195840157 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512816289 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124614359 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256399927 / 1.414213562 := by gcongr
      _ ≤ (0.000072339549 : ℝ) := by norm_num

end BstLean.Part269.N12480

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12480
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12480 BstLean.Part154.csC) (piBar (rhoBar 12480 BstLean.Part154.csC)) ≤ 1.65630E-7 := by
  have hr0 : 0 ≤ rhoBar 12480 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12480 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12480 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12480 BstLean.Part154.csC) (piBar (rhoBar 12480 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12480 BstLean.Part154.csC) (piBar (rhoBar 12480 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12480 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195840157 : ℝ) ^ 2 + 0.000124614359 ^ 2 + 3 * 0.000072339549 ^ 2 +
        2 * 0.797885 * 0.000195840157 * 0.000124614359 + 2 * 0.000195840157 * 0.000072339549 +
        4 * 0.797885 * 0.000124614359 * 0.000072339549 := by gcongr
    _ ≤ (1.65630E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12480 BstLean.Part154.csC Θ ≤ 0.002677284032 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12480 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12480 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12480 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12480 BstLean.Part154.csC) (piBar (rhoBar 12480 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12480 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036126256523 * 1.65630E-7 / (0.000256399530 : ℝ) := by gcongr
    _ ≤ 0.002677284032 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12480 BstLean.Part154.csC Θ ≤ 0.002971495629 + 0.000676504643 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12480 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12480 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12480 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036126256523 : ℝ) * ((2 * Θ * 0.000256399927 +
        (6863 / 10000) * 0.000256399927 * 12480 * 0.001025665449) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002971495629 + 0.000676504643 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12480 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12480 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12480 0.011 Θ ∧ gammaRatio 12480 0.011 Θ ≤ 0.000088143665 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12480 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036126256523 : ℝ) * 0.525 / ((1 - 0.011) * 12480) := by gcongr
      _ ≤ (0.000088143665 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12480 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12480 0.011 Θ) :=
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
    badAllowance 12480 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12480 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12480 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12480 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12480 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12480 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12480 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12480 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12480 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12480 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12480 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036126256523 : ℝ) * 12480 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12480 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003788834791 + 0.003353788675 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12480

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12480
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12480 BstLean.Part154.csC) (piBar (rhoBar 12480 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12480 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12480 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12480 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12480 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12480 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12480 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12480 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12480 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12480 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12480 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12480 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12480 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12480 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12480 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052949932099 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12480) ≤ 0.010690141187 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12480 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036126256523)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010690141187 + 2 * 0.737676 / 12480) := by gcongr
    _ ≤ (0.052949932099 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12480 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12480

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12480
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493443854 : ℝ) ≤ plow 12480 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12480) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053056173846)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405574117) : eMP 12480 0.011 xi bn ≤ 0.001209766628 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12480 : ℝ) * (1 - 0.011))) ≤ 0.000598131119 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001405574117 / (12480 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598131119 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598131119 : ℝ) + 3.141593 * 0.053056173846 / (12480 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001209766628 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053056173846)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405574117) : PiBarMP 12480 12 0.011 xi bn ≤ 0.162680881497 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12480 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037490987144 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.097794757591 : ℝ) ≤ √((12480 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.713920350151 : ℝ) ≤ √(12480 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12480) ≤ 0.124715059852 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037490987144 + 0.053056173846 * 1.772454 / (2 * (111.097794757591 : ℝ))) * (1 + 0.001209766628) +
        8 / (12480 * 111.713920350151) + 0.124715059852 := by gcongr
    _ ≤ (0.162680881497 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053056173846)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405574117) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283289190251) :
    parallelOracle 12480 0.011 xi bn cd ≤ 0.163689734504 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12480 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12480 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493443854 : ℝ) ≤ plow 12480 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.713920350151 : ℝ) ≤ √(12480 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283289190251 : ℝ) / (2 * 0.560493443854 * 111.713920350151)) * 0.162680881497 +
        0.283289190251 ^ 2 / (2 * 0.560493443854 * 111.713920350151) := by gcongr
    _ ≤ (0.163689734504 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053056173846) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405574117)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283289190251) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12480 12480 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493443854 : ℝ) ≤ plow 12480 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.713920350151 : ℝ) ≤ √(12480 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12480 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12480 Θ 1.22 ≤ 0.011870503657 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.713920350151 := by gcongr <;> linarith
      _ ≤ (0.011870503657 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12480 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12480 12480 0.011 ≤ 0.008556562073 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12480 12480 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12480 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12480 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12480 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12480 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163689734504 + 0.011870503657 + (0.008556562073 : ℝ) *
        (1 + 2 * (0.283289190251 + 0.011870503657) / (0.560493443854 * 111.713920350151))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12480]

end BstLean.Part269.N12480

/-! The original eight local profiles supply actual 12480 moment certificates. -/
namespace BstLean.Part269.N12480
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12480 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12480 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12480 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053056173846 ∧
    0 ≤ bN 12480 BstLean.Part154.csC (groupTheta g) ∧ bN 12480 BstLean.Part154.csC (groupTheta g) ≤ 0.001405574117 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12480 12480 0.011
      (momentAllowance 12480 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12480 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12480 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12480 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12480 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12480 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230339258152 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12480 0.011
      (momentAllowance 12480 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12480 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12480
/-! The actual computed-centre upper energy formula at 12480. -/
namespace BstLean.Part269.N12480
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12480

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12480
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12480)
open BstLean.Part268 (cell12480)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086160167701
  | 2 => 0.087115891446
  | 3 => 0.088071752940
  | 4 => 0.089029622425
  | 5 => 0.089991745718
  | 6 => 0.090960797828
  | 7 => 0.091939941221
  | 8 => 0.092932888718
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12480 12480 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12480 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12480

/-! Actual upper energy certificates on all 43 source endpoints at 12480. -/
namespace BstLean.Part269.N12480
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12480)
open BstLean.Part268 (cell12480)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12480 (gMinus 12480) (1 - (cell12480 i).lower) ≤ 1 ∧
    energyUpper 12480 (gMinus 12480) (BstLean.Part211.gPlus 12480)
      (finiteEnergy 12480 12480 0.011) (1 - (cell12480 i).lower) ≤
      (cell12480 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨10,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨11,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨12,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨13,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨14,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨15,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨16,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨17,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨18,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨19,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨20,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨21,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨22,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨23,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨24,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨25,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨26,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨27,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨28,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨29,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨30,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨31,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨32,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨33,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨34,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨35,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨36,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨37,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨38,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨39,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨40,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨41,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨42,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨43,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨44,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨45,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨46,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨47,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨48,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨49,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨50,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨51,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12480) (by norm_num)
        (q := 1 - (cell12480 ⟨52,by decide⟩).lower)
        (by norm_num [cell12480]) (by norm_num [cell12480])
      exact ⟨E.1,E.2.trans (by norm_num [cell12480])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12480

/-! Source-cell containment and simple scalar guards at 12480. -/
namespace BstLean.Part269.N12480
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12480)
open BstLean.Part268 (cell12480)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12480 ⟨10,by decide⟩).lower ∧ (cell12480 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12480 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12480 ⟨11,by decide⟩).lower ∧ (cell12480 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12480 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12480 ⟨12,by decide⟩).lower ∧ (cell12480 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12480 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12480 ⟨13,by decide⟩).lower ∧ (cell12480 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12480 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12480 ⟨14,by decide⟩).lower ∧ (cell12480 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12480 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12480 ⟨15,by decide⟩).lower ∧ (cell12480 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12480 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12480 ⟨16,by decide⟩).lower ∧ (cell12480 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12480 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12480 ⟨17,by decide⟩).lower ∧ (cell12480 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12480 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12480 ⟨18,by decide⟩).lower ∧ (cell12480 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12480 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12480 ⟨19,by decide⟩).lower ∧ (cell12480 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12480 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12480 ⟨20,by decide⟩).lower ∧ (cell12480 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12480 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12480 ⟨21,by decide⟩).lower ∧ (cell12480 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12480 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12480 ⟨22,by decide⟩).lower ∧ (cell12480 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12480 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12480 ⟨23,by decide⟩).lower ∧ (cell12480 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12480 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12480 ⟨24,by decide⟩).lower ∧ (cell12480 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12480 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12480 ⟨25,by decide⟩).lower ∧ (cell12480 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12480 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12480 ⟨26,by decide⟩).lower ∧ (cell12480 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12480 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12480 ⟨27,by decide⟩).lower ∧ (cell12480 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12480 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12480 ⟨28,by decide⟩).lower ∧ (cell12480 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12480 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12480 ⟨29,by decide⟩).lower ∧ (cell12480 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12480 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12480 ⟨30,by decide⟩).lower ∧ (cell12480 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12480 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12480 ⟨31,by decide⟩).lower ∧ (cell12480 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12480 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12480 ⟨32,by decide⟩).lower ∧ (cell12480 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12480 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12480 ⟨33,by decide⟩).lower ∧ (cell12480 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12480 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12480 ⟨34,by decide⟩).lower ∧ (cell12480 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12480 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12480 ⟨35,by decide⟩).lower ∧ (cell12480 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12480 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12480 ⟨36,by decide⟩).lower ∧ (cell12480 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12480 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12480 ⟨37,by decide⟩).lower ∧ (cell12480 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12480 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12480 ⟨38,by decide⟩).lower ∧ (cell12480 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12480 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12480 ⟨39,by decide⟩).lower ∧ (cell12480 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12480 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12480 ⟨40,by decide⟩).lower ∧ (cell12480 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12480 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12480 ⟨41,by decide⟩).lower ∧ (cell12480 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12480 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12480 ⟨42,by decide⟩).lower ∧ (cell12480 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12480 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12480 ⟨43,by decide⟩).lower ∧ (cell12480 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12480 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12480 ⟨44,by decide⟩).lower ∧ (cell12480 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12480 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12480 ⟨45,by decide⟩).lower ∧ (cell12480 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12480 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12480 ⟨46,by decide⟩).lower ∧ (cell12480 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12480 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12480 ⟨47,by decide⟩).lower ∧ (cell12480 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12480 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12480 ⟨48,by decide⟩).lower ∧ (cell12480 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12480 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12480 ⟨49,by decide⟩).lower ∧ (cell12480 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12480 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12480 ⟨50,by decide⟩).lower ∧ (cell12480 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12480 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12480 ⟨51,by decide⟩).lower ∧ (cell12480 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12480 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12480 ⟨52,by decide⟩).lower ∧ (cell12480 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12480 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12480 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12480 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12480,cell12480,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12480 i).lower ∧
    (cell12480 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12480 i).upper ≤ (0.532 : ℝ) ∧
    (cell12480 i).centre ≤ (0.1 : ℝ) ∧ (cell12480 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12480 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12480 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12480

/-! The local source numeric instances at 12480 have no network premises. -/
namespace BstLean.Part269.N12480
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12480)
open BstLean.Part268 (cell12480)

noncomputable def sourceNumerics12480 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12480 (cell12480 i)
      scalarRow12480.M scalarRow12480.H scalarRow12480.xi := by
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
    energy_allowance := scalarRow12480.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12480]
    centre_nonneg := (scalarRow12480.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12480])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12480
/-! Actual 12481 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12481
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12481 ≤ (1.036124796404 : ℝ) := by
  have hr : (111.718395978460 : ℝ) ≤ √(12481 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.718395978460 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12481 12481 (11 / 1000) ≤
    (0.008556219280 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12481) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.718395978460 : ℝ) ≤ √(12481 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12481)
  have hdiv : K / √(12481 : ℝ) ≤ K / 111.718395978460 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.718395978460 ≤ (0.008556219280 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12481.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12481 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12481 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12481 := gPlus_lower 12481
end BstLean.Part269.N12481

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12481
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036124796403 : ℝ) ≤ wn 12481 := by
  have hn : √(12481 : ℝ) ≤ 111.718395978461 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12481 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.718395978461 ≤ 2 / √(12481 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256378626 : ℝ) ≤ rhoBar 12481 BstLean.Part154.csC ∧
    rhoBar 12481 BstLean.Part154.csC ≤ 0.000256379023 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036124796403 : ℝ) / (1.295212 * 12481) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036124796404 : ℝ) / (1.29521 * 12481) := by gcongr
      _ ≤ (0.000256379023 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12481 BstLean.Part154.csC) ≤ 0.001025581823 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12481 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12481 BstLean.Part154.csC) (piBar (rhoBar 12481 BstLean.Part154.csC)) ≤ 0.000195824190 ∧
    cc1 (rhoBar 12481 BstLean.Part154.csC) (piBar (rhoBar 12481 BstLean.Part154.csC)) ≤ 0.000124604199 ∧
    cc2 (rhoBar 12481 BstLean.Part154.csC) ≤ 0.000072333651 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12481 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12481 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12481 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12481 BstLean.Part154.csC * nuR (rhoBar 12481 BstLean.Part154.csC)) ≤ 0.000512774479 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256379023 : ℝ) * 0.001025581823 := by gcongr
      _ ≤ (0.000512774479 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12481 BstLean.Part154.csC) * nuR (rhoBar 12481 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001025581823 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12481 BstLean.Part154.csC) * rhoBar 12481 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256379023 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256379023 / 2 + 0.399 * 0.001025581823 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195824190 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512774479 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124604199 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256379023 / 1.414213562 := by gcongr
      _ ≤ (0.000072333651 : ℝ) := by norm_num

end BstLean.Part269.N12481

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12481
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12481 BstLean.Part154.csC) (piBar (rhoBar 12481 BstLean.Part154.csC)) ≤ 1.65603E-7 := by
  have hr0 : 0 ≤ rhoBar 12481 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12481 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12481 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12481 BstLean.Part154.csC) (piBar (rhoBar 12481 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12481 BstLean.Part154.csC) (piBar (rhoBar 12481 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12481 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195824190 : ℝ) ^ 2 + 0.000124604199 ^ 2 + 3 * 0.000072333651 ^ 2 +
        2 * 0.797885 * 0.000195824190 * 0.000124604199 + 2 * 0.000195824190 * 0.000072333651 +
        4 * 0.797885 * 0.000124604199 * 0.000072333651 := by gcongr
    _ ≤ (1.65603E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12481 BstLean.Part154.csC Θ ≤ 0.002677062084 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12481 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12481 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12481 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12481 BstLean.Part154.csC) (piBar (rhoBar 12481 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12481 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036124796404 * 1.65603E-7 / (0.000256378626 : ℝ) := by gcongr
    _ ≤ 0.002677062084 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12481 BstLean.Part154.csC Θ ≤ 0.002971244984 + 0.000676448535 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12481 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12481 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12481 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036124796404 : ℝ) * ((2 * Θ * 0.000256379023 +
        (6863 / 10000) * 0.000256379023 * 12481 * 0.001025581823) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002971244984 + 0.000676448535 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12481 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12481 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12481 0.011 Θ ∧ gammaRatio 12481 0.011 Θ ≤ 0.000088136478 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12481 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036124796404 : ℝ) * 0.525 / ((1 - 0.011) * 12481) := by gcongr
      _ ≤ (0.000088136478 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12481 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12481 0.011 Θ) :=
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
    badAllowance 12481 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12481 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12481 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12481 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12481 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12481 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12481 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12481 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12481 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12481 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12481 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036124796404 : ℝ) * 12481 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12481 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003788584146 + 0.003353510619 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12481

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12481
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12481 BstLean.Part154.csC) (piBar (rhoBar 12481 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12481 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12481 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12481 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12481 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12481 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12481 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12481 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12481 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12481 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12481 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12481 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12481 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12481 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12481 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052947787635 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12481) ≤ 0.010689712922 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12481 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036124796404)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010689712922 + 2 * 0.737676 / 12481) := by gcongr
    _ ≤ (0.052947787635 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12481 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12481

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12481
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493490681 : ℝ) ≤ plow 12481 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12481) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053055777221)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405457595) : eMP 12481 0.011 xi bn ≤ 0.001209667936 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12481 : ℝ) * (1 - 0.011))) ≤ 0.000598082364 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001405457595 / (12481 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598082364 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598082364 : ℝ) + 3.141593 * 0.053055777221 / (12481 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001209667936 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053055777221)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405457595) : PiBarMP 12481 12 0.011 xi bn ≤ 0.162674304714 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12481 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037489433112 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.102245701875 : ℝ) ≤ √((12481 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.718395978460 : ℝ) ≤ √(12481 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12481) ≤ 0.124710063556 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037489433112 + 0.053055777221 * 1.772454 / (2 * (111.102245701875 : ℝ))) * (1 + 0.001209667936) +
        8 / (12481 * 111.718395978460) + 0.124710063556 := by gcongr
    _ ≤ (0.162674304714 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053055777221)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405457595) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283286184828) :
    parallelOracle 12481 0.011 xi bn cd ≤ 0.163683084843 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12481 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12481 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493490681 : ℝ) ≤ plow 12481 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.718395978460 : ℝ) ≤ √(12481 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283286184828 : ℝ) / (2 * 0.560493490681 * 111.718395978460)) * 0.162674304714 +
        0.283286184828 ^ 2 / (2 * 0.560493490681 * 111.718395978460) := by gcongr
    _ ≤ (0.163683084843 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053055777221) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405457595)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283286184828) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12481 12481 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493490681 : ℝ) ≤ plow 12481 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.718395978460 : ℝ) ≤ √(12481 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12481 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12481 Θ 1.22 ≤ 0.011870028105 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.718395978460 := by gcongr <;> linarith
      _ ≤ (0.011870028105 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12481 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12481 12481 0.011 ≤ 0.008556219280 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12481 12481 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12481 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12481 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12481 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12481 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163683084843 + 0.011870028105 + (0.008556219280 : ℝ) *
        (1 + 2 * (0.283286184828 + 0.011870028105) / (0.560493490681 * 111.718395978460))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12481]

end BstLean.Part269.N12481

/-! The original eight local profiles supply actual 12481 moment certificates. -/
namespace BstLean.Part269.N12481
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12481 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12481 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12481 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053055777221 ∧
    0 ≤ bN 12481 BstLean.Part154.csC (groupTheta g) ∧ bN 12481 BstLean.Part154.csC (groupTheta g) ≤ 0.001405457595 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12481 12481 0.011
      (momentAllowance 12481 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12481 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12481 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12481 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12481 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12481 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230338397193 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12481 0.011
      (momentAllowance 12481 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12481 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12481
/-! The actual computed-centre upper energy formula at 12481. -/
namespace BstLean.Part269.N12481
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12481

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12481
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12481)
open BstLean.Part268 (cell12481)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086156984341
  | 2 => 0.087112643202
  | 3 => 0.088068429347
  | 4 => 0.089026210686
  | 5 => 0.089988230307
  | 6 => 0.090957160047
  | 7 => 0.091936158706
  | 8 => 0.092928934894
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12481 12481 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12481 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12481

/-! Actual upper energy certificates on all 43 source endpoints at 12481. -/
namespace BstLean.Part269.N12481
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12481)
open BstLean.Part268 (cell12481)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12481 (gMinus 12481) (1 - (cell12481 i).lower) ≤ 1 ∧
    energyUpper 12481 (gMinus 12481) (BstLean.Part211.gPlus 12481)
      (finiteEnergy 12481 12481 0.011) (1 - (cell12481 i).lower) ≤
      (cell12481 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨10,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨11,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨12,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨13,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨14,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨15,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨16,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨17,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨18,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨19,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨20,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨21,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨22,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨23,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨24,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨25,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨26,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨27,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨28,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨29,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨30,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨31,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨32,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨33,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨34,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨35,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨36,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨37,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨38,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨39,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨40,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨41,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨42,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨43,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨44,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨45,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨46,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨47,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨48,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨49,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨50,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨51,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12481) (by norm_num)
        (q := 1 - (cell12481 ⟨52,by decide⟩).lower)
        (by norm_num [cell12481]) (by norm_num [cell12481])
      exact ⟨E.1,E.2.trans (by norm_num [cell12481])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12481

/-! Source-cell containment and simple scalar guards at 12481. -/
namespace BstLean.Part269.N12481
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12481)
open BstLean.Part268 (cell12481)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12481 ⟨10,by decide⟩).lower ∧ (cell12481 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12481 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12481 ⟨11,by decide⟩).lower ∧ (cell12481 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12481 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12481 ⟨12,by decide⟩).lower ∧ (cell12481 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12481 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12481 ⟨13,by decide⟩).lower ∧ (cell12481 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12481 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12481 ⟨14,by decide⟩).lower ∧ (cell12481 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12481 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12481 ⟨15,by decide⟩).lower ∧ (cell12481 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12481 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12481 ⟨16,by decide⟩).lower ∧ (cell12481 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12481 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12481 ⟨17,by decide⟩).lower ∧ (cell12481 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12481 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12481 ⟨18,by decide⟩).lower ∧ (cell12481 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12481 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12481 ⟨19,by decide⟩).lower ∧ (cell12481 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12481 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12481 ⟨20,by decide⟩).lower ∧ (cell12481 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12481 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12481 ⟨21,by decide⟩).lower ∧ (cell12481 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12481 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12481 ⟨22,by decide⟩).lower ∧ (cell12481 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12481 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12481 ⟨23,by decide⟩).lower ∧ (cell12481 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12481 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12481 ⟨24,by decide⟩).lower ∧ (cell12481 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12481 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12481 ⟨25,by decide⟩).lower ∧ (cell12481 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12481 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12481 ⟨26,by decide⟩).lower ∧ (cell12481 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12481 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12481 ⟨27,by decide⟩).lower ∧ (cell12481 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12481 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12481 ⟨28,by decide⟩).lower ∧ (cell12481 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12481 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12481 ⟨29,by decide⟩).lower ∧ (cell12481 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12481 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12481 ⟨30,by decide⟩).lower ∧ (cell12481 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12481 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12481 ⟨31,by decide⟩).lower ∧ (cell12481 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12481 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12481 ⟨32,by decide⟩).lower ∧ (cell12481 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12481 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12481 ⟨33,by decide⟩).lower ∧ (cell12481 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12481 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12481 ⟨34,by decide⟩).lower ∧ (cell12481 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12481 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12481 ⟨35,by decide⟩).lower ∧ (cell12481 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12481 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12481 ⟨36,by decide⟩).lower ∧ (cell12481 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12481 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12481 ⟨37,by decide⟩).lower ∧ (cell12481 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12481 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12481 ⟨38,by decide⟩).lower ∧ (cell12481 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12481 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12481 ⟨39,by decide⟩).lower ∧ (cell12481 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12481 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12481 ⟨40,by decide⟩).lower ∧ (cell12481 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12481 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12481 ⟨41,by decide⟩).lower ∧ (cell12481 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12481 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12481 ⟨42,by decide⟩).lower ∧ (cell12481 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12481 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12481 ⟨43,by decide⟩).lower ∧ (cell12481 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12481 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12481 ⟨44,by decide⟩).lower ∧ (cell12481 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12481 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12481 ⟨45,by decide⟩).lower ∧ (cell12481 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12481 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12481 ⟨46,by decide⟩).lower ∧ (cell12481 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12481 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12481 ⟨47,by decide⟩).lower ∧ (cell12481 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12481 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12481 ⟨48,by decide⟩).lower ∧ (cell12481 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12481 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12481 ⟨49,by decide⟩).lower ∧ (cell12481 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12481 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12481 ⟨50,by decide⟩).lower ∧ (cell12481 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12481 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12481 ⟨51,by decide⟩).lower ∧ (cell12481 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12481 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12481 ⟨52,by decide⟩).lower ∧ (cell12481 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12481 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12481 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12481 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12481,cell12481,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12481 i).lower ∧
    (cell12481 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12481 i).upper ≤ (0.532 : ℝ) ∧
    (cell12481 i).centre ≤ (0.1 : ℝ) ∧ (cell12481 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12481 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12481 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12481

/-! The local source numeric instances at 12481 have no network premises. -/
namespace BstLean.Part269.N12481
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12481)
open BstLean.Part268 (cell12481)

noncomputable def sourceNumerics12481 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12481 (cell12481 i)
      scalarRow12481.M scalarRow12481.H scalarRow12481.xi := by
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
    energy_allowance := scalarRow12481.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12481]
    centre_nonneg := (scalarRow12481.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12481])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12481
/-! Actual 12482 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12482
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12482 ≤ (1.036123336462 : ℝ) := by
  have hr : (111.722871427474 : ℝ) ≤ √(12482 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.722871427474 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12482 12482 (11 / 1000) ≤
    (0.008555876528 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12482) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.722871427474 : ℝ) ≤ √(12482 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12482)
  have hdiv : K / √(12482 : ℝ) ≤ K / 111.722871427474 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.722871427474 ≤ (0.008555876528 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12482.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12482 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12482 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12482 := gPlus_lower 12482
end BstLean.Part269.N12482

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12482
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036123336461 : ℝ) ≤ wn 12482 := by
  have hn : √(12482 : ℝ) ≤ 111.722871427475 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12482 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.722871427475 ≤ 2 / √(12482 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256357725 : ℝ) ≤ rhoBar 12482 BstLean.Part154.csC ∧
    rhoBar 12482 BstLean.Part154.csC ≤ 0.000256358121 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036123336461 : ℝ) / (1.295212 * 12482) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036123336462 : ℝ) / (1.29521 * 12482) := by gcongr
      _ ≤ (0.000256358121 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12482 BstLean.Part154.csC) ≤ 0.001025498204 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12482 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12482 BstLean.Part154.csC) (piBar (rhoBar 12482 BstLean.Part154.csC)) ≤ 0.000195808224 ∧
    cc1 (rhoBar 12482 BstLean.Part154.csC) (piBar (rhoBar 12482 BstLean.Part154.csC)) ≤ 0.000124594040 ∧
    cc2 (rhoBar 12482 BstLean.Part154.csC) ≤ 0.000072327754 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12482 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12482 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12482 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12482 BstLean.Part154.csC * nuR (rhoBar 12482 BstLean.Part154.csC)) ≤ 0.000512732672 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256358121 : ℝ) * 0.001025498204 := by gcongr
      _ ≤ (0.000512732672 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12482 BstLean.Part154.csC) * nuR (rhoBar 12482 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001025498204 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12482 BstLean.Part154.csC) * rhoBar 12482 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256358121 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256358121 / 2 + 0.399 * 0.001025498204 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195808224 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512732672 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124594040 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256358121 / 1.414213562 := by gcongr
      _ ≤ (0.000072327754 : ℝ) := by norm_num

end BstLean.Part269.N12482

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12482
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12482 BstLean.Part154.csC) (piBar (rhoBar 12482 BstLean.Part154.csC)) ≤ 1.65576E-7 := by
  have hr0 : 0 ≤ rhoBar 12482 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12482 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12482 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12482 BstLean.Part154.csC) (piBar (rhoBar 12482 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12482 BstLean.Part154.csC) (piBar (rhoBar 12482 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12482 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195808224 : ℝ) ^ 2 + 0.000124594040 ^ 2 + 3 * 0.000072327754 ^ 2 +
        2 * 0.797885 * 0.000195808224 * 0.000124594040 + 2 * 0.000195808224 * 0.000072327754 +
        4 * 0.797885 * 0.000124594040 * 0.000072327754 := by gcongr
    _ ≤ (1.65576E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12482 BstLean.Part154.csC Θ ≤ 0.002676840069 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12482 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12482 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12482 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12482 BstLean.Part154.csC) (piBar (rhoBar 12482 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12482 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036123336462 * 1.65576E-7 / (0.000256357725 : ℝ) := by gcongr
    _ ≤ 0.002676840069 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12482 BstLean.Part154.csC Θ ≤ 0.002970994347 + 0.000676392433 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12482 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12482 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12482 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036123336462 : ℝ) * ((2 * Θ * 0.000256358121 +
        (6863 / 10000) * 0.000256358121 * 12482 * 0.001025498204) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002970994347 + 0.000676392433 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12482 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12482 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12482 0.011 Θ ∧ gammaRatio 12482 0.011 Θ ≤ 0.000088129293 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12482 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036123336462 : ℝ) * 0.525 / ((1 - 0.011) * 12482) := by gcongr
      _ ≤ (0.000088129293 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12482 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12482 0.011 Θ) :=
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
    badAllowance 12482 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12482 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12482 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12482 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12482 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12482 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12482 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12482 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12482 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12482 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12482 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036123336462 : ℝ) * 12482 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12482 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003788333509 + 0.003353232502 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12482

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12482
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12482 BstLean.Part154.csC) (piBar (rhoBar 12482 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12482 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12482 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12482 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12482 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12482 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12482 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12482 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12482 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12482 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12482 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12482 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12482 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12482 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12482 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052945643429 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12482) ≤ 0.010689284708 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12482 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036123336462)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010689284708 + 2 * 0.737676 / 12482) := by gcongr
    _ ≤ (0.052945643429 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12482 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12482

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12482
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493537502 : ℝ) ≤ plow 12482 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12482) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053055380573)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405341037) : eMP 12482 0.011 xi bn ≤ 0.001209569237 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12482 : ℝ) * (1 - 0.011))) ≤ 0.000598033606 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001405341037 / (12482 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000598033606 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000598033606 : ℝ) + 3.141593 * 0.053055380573 / (12482 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001209569237 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053055380573)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405341037) : PiBarMP 12482 12 0.011 xi bn ≤ 0.162667727987 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12482 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037487878535 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.106696467854 : ℝ) ≤ √((12482 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.722871427474 : ℝ) ≤ √(12482 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12482) ≤ 0.124705067859 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037487878535 + 0.053055380573 * 1.772454 / (2 * (111.106696467854 : ℝ))) * (1 + 0.001209569237) +
        8 / (12482 * 111.722871427474) + 0.124705067859 := by gcongr
    _ ≤ (0.162667727987 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053055380573)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405341037) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283283179608) :
    parallelOracle 12482 0.011 xi bn cd ≤ 0.163676435246 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12482 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12482 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493537502 : ℝ) ≤ plow 12482 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.722871427474 : ℝ) ≤ √(12482 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283283179608 : ℝ) / (2 * 0.560493537502 * 111.722871427474)) * 0.162667727987 +
        0.283283179608 ^ 2 / (2 * 0.560493537502 * 111.722871427474) := by gcongr
    _ ≤ (0.163676435246 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053055380573) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405341037)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283283179608) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12482 12482 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493537502 : ℝ) ≤ plow 12482 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.722871427474 : ℝ) ≤ √(12482 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12482 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12482 Θ 1.22 ≤ 0.011869552609 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.722871427474 := by gcongr <;> linarith
      _ ≤ (0.011869552609 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12482 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12482 12482 0.011 ≤ 0.008555876528 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12482 12482 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12482 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12482 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12482 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12482 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163676435246 + 0.011869552609 + (0.008555876528 : ℝ) *
        (1 + 2 * (0.283283179608 + 0.011869552609) / (0.560493537502 * 111.722871427474))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12482]

end BstLean.Part269.N12482

/-! The original eight local profiles supply actual 12482 moment certificates. -/
namespace BstLean.Part269.N12482
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12482 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12482 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12482 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053055380573 ∧
    0 ≤ bN 12482 BstLean.Part154.csC (groupTheta g) ∧ bN 12482 BstLean.Part154.csC (groupTheta g) ≤ 0.001405341037 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12482 12482 0.011
      (momentAllowance 12482 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12482 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12482 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12482 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12482 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12482 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230337536179 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12482 0.011
      (momentAllowance 12482 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12482 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12482
/-! The actual computed-centre upper energy formula at 12482. -/
namespace BstLean.Part269.N12482
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12482

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12482
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12482)
open BstLean.Part268 (cell12482)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086153802342
  | 2 => 0.087109396380
  | 3 => 0.088065107248
  | 4 => 0.089022800530
  | 5 => 0.089984716590
  | 6 => 0.090953524093
  | 7 => 0.091932378177
  | 8 => 0.092924983247
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12482 12482 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12482 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12482

/-! Actual upper energy certificates on all 43 source endpoints at 12482. -/
namespace BstLean.Part269.N12482
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12482)
open BstLean.Part268 (cell12482)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12482 (gMinus 12482) (1 - (cell12482 i).lower) ≤ 1 ∧
    energyUpper 12482 (gMinus 12482) (BstLean.Part211.gPlus 12482)
      (finiteEnergy 12482 12482 0.011) (1 - (cell12482 i).lower) ≤
      (cell12482 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨10,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨11,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨12,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨13,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨14,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨15,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨16,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨17,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨18,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨19,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨20,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨21,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨22,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨23,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨24,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨25,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨26,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨27,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨28,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨29,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨30,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨31,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨32,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨33,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨34,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨35,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨36,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨37,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨38,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨39,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨40,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨41,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨42,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨43,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨44,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨45,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨46,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨47,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨48,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨49,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨50,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨51,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12482) (by norm_num)
        (q := 1 - (cell12482 ⟨52,by decide⟩).lower)
        (by norm_num [cell12482]) (by norm_num [cell12482])
      exact ⟨E.1,E.2.trans (by norm_num [cell12482])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12482

/-! Source-cell containment and simple scalar guards at 12482. -/
namespace BstLean.Part269.N12482
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12482)
open BstLean.Part268 (cell12482)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12482 ⟨10,by decide⟩).lower ∧ (cell12482 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12482 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12482 ⟨11,by decide⟩).lower ∧ (cell12482 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12482 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12482 ⟨12,by decide⟩).lower ∧ (cell12482 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12482 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12482 ⟨13,by decide⟩).lower ∧ (cell12482 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12482 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12482 ⟨14,by decide⟩).lower ∧ (cell12482 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12482 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12482 ⟨15,by decide⟩).lower ∧ (cell12482 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12482 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12482 ⟨16,by decide⟩).lower ∧ (cell12482 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12482 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12482 ⟨17,by decide⟩).lower ∧ (cell12482 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12482 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12482 ⟨18,by decide⟩).lower ∧ (cell12482 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12482 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12482 ⟨19,by decide⟩).lower ∧ (cell12482 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12482 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12482 ⟨20,by decide⟩).lower ∧ (cell12482 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12482 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12482 ⟨21,by decide⟩).lower ∧ (cell12482 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12482 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12482 ⟨22,by decide⟩).lower ∧ (cell12482 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12482 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12482 ⟨23,by decide⟩).lower ∧ (cell12482 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12482 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12482 ⟨24,by decide⟩).lower ∧ (cell12482 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12482 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12482 ⟨25,by decide⟩).lower ∧ (cell12482 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12482 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12482 ⟨26,by decide⟩).lower ∧ (cell12482 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12482 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12482 ⟨27,by decide⟩).lower ∧ (cell12482 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12482 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12482 ⟨28,by decide⟩).lower ∧ (cell12482 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12482 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12482 ⟨29,by decide⟩).lower ∧ (cell12482 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12482 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12482 ⟨30,by decide⟩).lower ∧ (cell12482 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12482 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12482 ⟨31,by decide⟩).lower ∧ (cell12482 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12482 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12482 ⟨32,by decide⟩).lower ∧ (cell12482 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12482 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12482 ⟨33,by decide⟩).lower ∧ (cell12482 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12482 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12482 ⟨34,by decide⟩).lower ∧ (cell12482 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12482 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12482 ⟨35,by decide⟩).lower ∧ (cell12482 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12482 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12482 ⟨36,by decide⟩).lower ∧ (cell12482 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12482 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12482 ⟨37,by decide⟩).lower ∧ (cell12482 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12482 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12482 ⟨38,by decide⟩).lower ∧ (cell12482 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12482 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12482 ⟨39,by decide⟩).lower ∧ (cell12482 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12482 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12482 ⟨40,by decide⟩).lower ∧ (cell12482 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12482 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12482 ⟨41,by decide⟩).lower ∧ (cell12482 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12482 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12482 ⟨42,by decide⟩).lower ∧ (cell12482 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12482 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12482 ⟨43,by decide⟩).lower ∧ (cell12482 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12482 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12482 ⟨44,by decide⟩).lower ∧ (cell12482 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12482 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12482 ⟨45,by decide⟩).lower ∧ (cell12482 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12482 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12482 ⟨46,by decide⟩).lower ∧ (cell12482 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12482 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12482 ⟨47,by decide⟩).lower ∧ (cell12482 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12482 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12482 ⟨48,by decide⟩).lower ∧ (cell12482 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12482 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12482 ⟨49,by decide⟩).lower ∧ (cell12482 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12482 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12482 ⟨50,by decide⟩).lower ∧ (cell12482 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12482 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12482 ⟨51,by decide⟩).lower ∧ (cell12482 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12482 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12482 ⟨52,by decide⟩).lower ∧ (cell12482 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12482 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12482 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12482 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12482,cell12482,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12482 i).lower ∧
    (cell12482 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12482 i).upper ≤ (0.532 : ℝ) ∧
    (cell12482 i).centre ≤ (0.1 : ℝ) ∧ (cell12482 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12482 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12482 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12482

/-! The local source numeric instances at 12482 have no network premises. -/
namespace BstLean.Part269.N12482
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12482)
open BstLean.Part268 (cell12482)

noncomputable def sourceNumerics12482 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12482 (cell12482 i)
      scalarRow12482.M scalarRow12482.H scalarRow12482.xi := by
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
    energy_allowance := scalarRow12482.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12482]
    centre_nonneg := (scalarRow12482.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12482])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12482
/-! Actual 12483 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12483
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12483 ≤ (1.036121876696 : ℝ) := by
  have hr : (111.727346697216 : ℝ) ≤ √(12483 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.727346697216 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12483 12483 (11 / 1000) ≤
    (0.008555533817 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12483) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.727346697216 : ℝ) ≤ √(12483 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12483)
  have hdiv : K / √(12483 : ℝ) ≤ K / 111.727346697216 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.727346697216 ≤ (0.008555533817 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12483.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12483 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12483 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12483 := gPlus_lower 12483
end BstLean.Part269.N12483

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12483
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036121876695 : ℝ) ≤ wn 12483 := by
  have hn : √(12483 : ℝ) ≤ 111.727346697217 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12483 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.727346697217 ≤ 2 / √(12483 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256336827 : ℝ) ≤ rhoBar 12483 BstLean.Part154.csC ∧
    rhoBar 12483 BstLean.Part154.csC ≤ 0.000256337224 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036121876695 : ℝ) / (1.295212 * 12483) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036121876696 : ℝ) / (1.29521 * 12483) := by gcongr
      _ ≤ (0.000256337224 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12483 BstLean.Part154.csC) ≤ 0.001025414605 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12483 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12483 BstLean.Part154.csC) (piBar (rhoBar 12483 BstLean.Part154.csC)) ≤ 0.000195792262 ∧
    cc1 (rhoBar 12483 BstLean.Part154.csC) (piBar (rhoBar 12483 BstLean.Part154.csC)) ≤ 0.000124583883 ∧
    cc2 (rhoBar 12483 BstLean.Part154.csC) ≤ 0.000072321858 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12483 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12483 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12483 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12483 BstLean.Part154.csC * nuR (rhoBar 12483 BstLean.Part154.csC)) ≤ 0.000512690875 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256337224 : ℝ) * 0.001025414605 := by gcongr
      _ ≤ (0.000512690875 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12483 BstLean.Part154.csC) * nuR (rhoBar 12483 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001025414605 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12483 BstLean.Part154.csC) * rhoBar 12483 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256337224 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256337224 / 2 + 0.399 * 0.001025414605 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195792262 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512690875 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124583883 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256337224 / 1.414213562 := by gcongr
      _ ≤ (0.000072321858 : ℝ) := by norm_num

end BstLean.Part269.N12483

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12483
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12483 BstLean.Part154.csC) (piBar (rhoBar 12483 BstLean.Part154.csC)) ≤ 1.65549E-7 := by
  have hr0 : 0 ≤ rhoBar 12483 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12483 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12483 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12483 BstLean.Part154.csC) (piBar (rhoBar 12483 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12483 BstLean.Part154.csC) (piBar (rhoBar 12483 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12483 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195792262 : ℝ) ^ 2 + 0.000124583883 ^ 2 + 3 * 0.000072321858 ^ 2 +
        2 * 0.797885 * 0.000195792262 * 0.000124583883 + 2 * 0.000195792262 * 0.000072321858 +
        4 * 0.797885 * 0.000124583883 * 0.000072321858 := by gcongr
    _ ≤ (1.65549E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12483 BstLean.Part154.csC Θ ≤ 0.002676617989 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12483 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12483 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12483 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12483 BstLean.Part154.csC) (piBar (rhoBar 12483 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12483 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036121876696 * 1.65549E-7 / (0.000256336827 : ℝ) := by gcongr
    _ ≤ 0.002676617989 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12483 BstLean.Part154.csC Θ ≤ 0.002970743788 + 0.000676336344 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12483 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12483 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12483 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036121876696 : ℝ) * ((2 * Θ * 0.000256337224 +
        (6863 / 10000) * 0.000256337224 * 12483 * 0.001025414605) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002970743788 + 0.000676336344 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12483 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12483 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12483 0.011 Θ ∧ gammaRatio 12483 0.011 Θ ≤ 0.000088122109 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12483 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036121876696 : ℝ) * 0.525 / ((1 - 0.011) * 12483) := by gcongr
      _ ≤ (0.000088122109 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12483 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12483 0.011 Θ) :=
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
    badAllowance 12483 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12483 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12483 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12483 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12483 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12483 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12483 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12483 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12483 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12483 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12483 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036121876696 : ℝ) * 12483 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12483 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003788082950 + 0.003352954333 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12483

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12483
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12483 BstLean.Part154.csC) (piBar (rhoBar 12483 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12483 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12483 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12483 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12483 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12483 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12483 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12483 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12483 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12483 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12483 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12483 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12483 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12483 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12483 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052943499484 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12483) ≤ 0.010688856546 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12483 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036121876696)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010688856546 + 2 * 0.737676 / 12483) := by gcongr
    _ ≤ (0.052943499484 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12483 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12483

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12483
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493584314 : ℝ) ≤ plow 12483 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12483) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053054983975)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405224445) : eMP 12483 0.011 xi bn ≤ 0.001209470532 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12483 : ℝ) * (1 - 0.011))) ≤ 0.000597984845 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001405224445 / (12483 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597984845 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597984845 : ℝ) + 3.141593 * 0.053054983975 / (12483 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001209470532 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053054983975)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405224445) : PiBarMP 12483 12 0.011 xi bn ≤ 0.162661151345 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12483 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037486323440 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.111147055549 : ℝ) ≤ √((12483 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.727346697216 : ℝ) ≤ √(12483 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12483) ≤ 0.124700072763 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037486323440 + 0.053054983975 * 1.772454 / (2 * (111.111147055549 : ℝ))) * (1 + 0.001209470532) +
        8 / (12483 * 111.727346697216) + 0.124700072763 := by gcongr
    _ ≤ (0.162661151345 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053054983975)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405224445) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283280174756) :
    parallelOracle 12483 0.011 xi bn cd ≤ 0.163669785746 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12483 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12483 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493584314 : ℝ) ≤ plow 12483 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.727346697216 : ℝ) ≤ √(12483 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283280174756 : ℝ) / (2 * 0.560493584314 * 111.727346697216)) * 0.162661151345 +
        0.283280174756 ^ 2 / (2 * 0.560493584314 * 111.727346697216) := by gcongr
    _ ≤ (0.163669785746 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053054983975) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405224445)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283280174756) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12483 12483 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493584314 : ℝ) ≤ plow 12483 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.727346697216 : ℝ) ≤ √(12483 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12483 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12483 Θ 1.22 ≤ 0.011869077171 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.727346697216 := by gcongr <;> linarith
      _ ≤ (0.011869077171 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12483 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12483 12483 0.011 ≤ 0.008555533817 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12483 12483 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12483 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12483 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12483 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12483 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163669785746 + 0.011869077171 + (0.008555533817 : ℝ) *
        (1 + 2 * (0.283280174756 + 0.011869077171) / (0.560493584314 * 111.727346697216))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12483]

end BstLean.Part269.N12483

/-! The original eight local profiles supply actual 12483 moment certificates. -/
namespace BstLean.Part269.N12483
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12483 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12483 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12483 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053054983975 ∧
    0 ≤ bN 12483 BstLean.Part154.csC (groupTheta g) ∧ bN 12483 BstLean.Part154.csC (groupTheta g) ≤ 0.001405224445 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12483 12483 0.011
      (momentAllowance 12483 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12483 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12483 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12483 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12483 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12483 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230336675272 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12483 0.011
      (momentAllowance 12483 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12483 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12483
/-! The actual computed-centre upper energy formula at 12483. -/
namespace BstLean.Part269.N12483
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12483

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12483
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12483)
open BstLean.Part268 (cell12483)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086150621704
  | 2 => 0.087106150977
  | 3 => 0.088061786642
  | 4 => 0.089019391957
  | 5 => 0.089981204563
  | 6 => 0.090949889961
  | 7 => 0.091928599631
  | 8 => 0.092921033776
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12483 12483 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12483 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12483

/-! Actual upper energy certificates on all 43 source endpoints at 12483. -/
namespace BstLean.Part269.N12483
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12483)
open BstLean.Part268 (cell12483)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12483 (gMinus 12483) (1 - (cell12483 i).lower) ≤ 1 ∧
    energyUpper 12483 (gMinus 12483) (BstLean.Part211.gPlus 12483)
      (finiteEnergy 12483 12483 0.011) (1 - (cell12483 i).lower) ≤
      (cell12483 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨10,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨11,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨12,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨13,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨14,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨15,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨16,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨17,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨18,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨19,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨20,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨21,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨22,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨23,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨24,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨25,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨26,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨27,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨28,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨29,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨30,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨31,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨32,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨33,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨34,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨35,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨36,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨37,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨38,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨39,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨40,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨41,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨42,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨43,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨44,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨45,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨46,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨47,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨48,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨49,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨50,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨51,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12483) (by norm_num)
        (q := 1 - (cell12483 ⟨52,by decide⟩).lower)
        (by norm_num [cell12483]) (by norm_num [cell12483])
      exact ⟨E.1,E.2.trans (by norm_num [cell12483])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12483

/-! Source-cell containment and simple scalar guards at 12483. -/
namespace BstLean.Part269.N12483
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12483)
open BstLean.Part268 (cell12483)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12483 ⟨10,by decide⟩).lower ∧ (cell12483 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12483 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12483 ⟨11,by decide⟩).lower ∧ (cell12483 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12483 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12483 ⟨12,by decide⟩).lower ∧ (cell12483 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12483 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12483 ⟨13,by decide⟩).lower ∧ (cell12483 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12483 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12483 ⟨14,by decide⟩).lower ∧ (cell12483 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12483 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12483 ⟨15,by decide⟩).lower ∧ (cell12483 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12483 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12483 ⟨16,by decide⟩).lower ∧ (cell12483 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12483 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12483 ⟨17,by decide⟩).lower ∧ (cell12483 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12483 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12483 ⟨18,by decide⟩).lower ∧ (cell12483 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12483 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12483 ⟨19,by decide⟩).lower ∧ (cell12483 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12483 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12483 ⟨20,by decide⟩).lower ∧ (cell12483 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12483 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12483 ⟨21,by decide⟩).lower ∧ (cell12483 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12483 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12483 ⟨22,by decide⟩).lower ∧ (cell12483 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12483 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12483 ⟨23,by decide⟩).lower ∧ (cell12483 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12483 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12483 ⟨24,by decide⟩).lower ∧ (cell12483 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12483 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12483 ⟨25,by decide⟩).lower ∧ (cell12483 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12483 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12483 ⟨26,by decide⟩).lower ∧ (cell12483 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12483 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12483 ⟨27,by decide⟩).lower ∧ (cell12483 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12483 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12483 ⟨28,by decide⟩).lower ∧ (cell12483 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12483 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12483 ⟨29,by decide⟩).lower ∧ (cell12483 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12483 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12483 ⟨30,by decide⟩).lower ∧ (cell12483 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12483 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12483 ⟨31,by decide⟩).lower ∧ (cell12483 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12483 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12483 ⟨32,by decide⟩).lower ∧ (cell12483 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12483 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12483 ⟨33,by decide⟩).lower ∧ (cell12483 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12483 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12483 ⟨34,by decide⟩).lower ∧ (cell12483 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12483 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12483 ⟨35,by decide⟩).lower ∧ (cell12483 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12483 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12483 ⟨36,by decide⟩).lower ∧ (cell12483 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12483 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12483 ⟨37,by decide⟩).lower ∧ (cell12483 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12483 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12483 ⟨38,by decide⟩).lower ∧ (cell12483 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12483 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12483 ⟨39,by decide⟩).lower ∧ (cell12483 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12483 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12483 ⟨40,by decide⟩).lower ∧ (cell12483 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12483 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12483 ⟨41,by decide⟩).lower ∧ (cell12483 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12483 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12483 ⟨42,by decide⟩).lower ∧ (cell12483 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12483 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12483 ⟨43,by decide⟩).lower ∧ (cell12483 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12483 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12483 ⟨44,by decide⟩).lower ∧ (cell12483 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12483 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12483 ⟨45,by decide⟩).lower ∧ (cell12483 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12483 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12483 ⟨46,by decide⟩).lower ∧ (cell12483 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12483 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12483 ⟨47,by decide⟩).lower ∧ (cell12483 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12483 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12483 ⟨48,by decide⟩).lower ∧ (cell12483 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12483 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12483 ⟨49,by decide⟩).lower ∧ (cell12483 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12483 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12483 ⟨50,by decide⟩).lower ∧ (cell12483 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12483 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12483 ⟨51,by decide⟩).lower ∧ (cell12483 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12483 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12483 ⟨52,by decide⟩).lower ∧ (cell12483 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12483 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12483 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12483 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12483,cell12483,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12483 i).lower ∧
    (cell12483 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12483 i).upper ≤ (0.532 : ℝ) ∧
    (cell12483 i).centre ≤ (0.1 : ℝ) ∧ (cell12483 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12483 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12483 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12483

/-! The local source numeric instances at 12483 have no network premises. -/
namespace BstLean.Part269.N12483
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12483)
open BstLean.Part268 (cell12483)

noncomputable def sourceNumerics12483 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12483 (cell12483 i)
      scalarRow12483.M scalarRow12483.H scalarRow12483.xi := by
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
    energy_allowance := scalarRow12483.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12483]
    centre_nonneg := (scalarRow12483.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12483])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12483
/-! Actual 12484 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12484
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12484 ≤ (1.036120417106 : ℝ) := by
  have hr : (111.731821787707 : ℝ) ≤ √(12484 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.731821787707 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12484 12484 (11 / 1000) ≤
    (0.008555191148 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12484) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.731821787707 : ℝ) ≤ √(12484 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12484)
  have hdiv : K / √(12484 : ℝ) ≤ K / 111.731821787707 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.731821787707 ≤ (0.008555191148 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12484.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12484 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12484 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12484 := gPlus_lower 12484
end BstLean.Part269.N12484

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12484
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036120417105 : ℝ) ≤ wn 12484 := by
  have hn : √(12484 : ℝ) ≤ 111.731821787708 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12484 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.731821787708 ≤ 2 / √(12484 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256315933 : ℝ) ≤ rhoBar 12484 BstLean.Part154.csC ∧
    rhoBar 12484 BstLean.Part154.csC ≤ 0.000256316329 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036120417105 : ℝ) / (1.295212 * 12484) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036120417106 : ℝ) / (1.29521 * 12484) := by gcongr
      _ ≤ (0.000256316329 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12484 BstLean.Part154.csC) ≤ 0.001025331015 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12484 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12484 BstLean.Part154.csC) (piBar (rhoBar 12484 BstLean.Part154.csC)) ≤ 0.000195776302 ∧
    cc1 (rhoBar 12484 BstLean.Part154.csC) (piBar (rhoBar 12484 BstLean.Part154.csC)) ≤ 0.000124573728 ∧
    cc2 (rhoBar 12484 BstLean.Part154.csC) ≤ 0.000072315963 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12484 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12484 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12484 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12484 BstLean.Part154.csC * nuR (rhoBar 12484 BstLean.Part154.csC)) ≤ 0.000512649083 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256316329 : ℝ) * 0.001025331015 := by gcongr
      _ ≤ (0.000512649083 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12484 BstLean.Part154.csC) * nuR (rhoBar 12484 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001025331015 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12484 BstLean.Part154.csC) * rhoBar 12484 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256316329 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256316329 / 2 + 0.399 * 0.001025331015 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195776302 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512649083 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124573728 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256316329 / 1.414213562 := by gcongr
      _ ≤ (0.000072315963 : ℝ) := by norm_num

end BstLean.Part269.N12484

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12484
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12484 BstLean.Part154.csC) (piBar (rhoBar 12484 BstLean.Part154.csC)) ≤ 1.65522E-7 := by
  have hr0 : 0 ≤ rhoBar 12484 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12484 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12484 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12484 BstLean.Part154.csC) (piBar (rhoBar 12484 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12484 BstLean.Part154.csC) (piBar (rhoBar 12484 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12484 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195776302 : ℝ) ^ 2 + 0.000124573728 ^ 2 + 3 * 0.000072315963 ^ 2 +
        2 * 0.797885 * 0.000195776302 * 0.000124573728 + 2 * 0.000195776302 * 0.000072315963 +
        4 * 0.797885 * 0.000124573728 * 0.000072315963 := by gcongr
    _ ≤ (1.65522E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12484 BstLean.Part154.csC Θ ≤ 0.002676395832 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12484 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12484 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12484 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12484 BstLean.Part154.csC) (piBar (rhoBar 12484 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12484 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036120417106 * 1.65522E-7 / (0.000256315933 : ℝ) := by gcongr
    _ ≤ 0.002676395832 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12484 BstLean.Part154.csC Θ ≤ 0.002970493241 + 0.000676280260 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12484 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12484 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12484 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036120417106 : ℝ) * ((2 * Θ * 0.000256316329 +
        (6863 / 10000) * 0.000256316329 * 12484 * 0.001025331015) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002970493241 + 0.000676280260 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12484 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12484 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12484 0.011 Θ ∧ gammaRatio 12484 0.011 Θ ≤ 0.000088114926 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12484 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036120417106 : ℝ) * 0.525 / ((1 - 0.011) * 12484) := by gcongr
      _ ≤ (0.000088114926 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12484 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12484 0.011 Θ) :=
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
    badAllowance 12484 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12484 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12484 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12484 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12484 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12484 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12484 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12484 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12484 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12484 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12484 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036120417106 : ℝ) * 12484 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12484 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003787832403 + 0.003352676092 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12484

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12484
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12484 BstLean.Part154.csC) (piBar (rhoBar 12484 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12484 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12484 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12484 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12484 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12484 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12484 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12484 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12484 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12484 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12484 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12484 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12484 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12484 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12484 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052941355797 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12484) ≤ 0.010688428435 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12484 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036120417106)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010688428435 + 2 * 0.737676 / 12484) := by gcongr
    _ ≤ (0.052941355797 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12484 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12484

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12484
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493631119 : ℝ) ≤ plow 12484 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12484) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053054587352)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405107812) : eMP 12484 0.011 xi bn ≤ 0.001209371818 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12484 : ℝ) * (1 - 0.011))) ≤ 0.000597936079 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001405107812 / (12484 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597936079 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597936079 : ℝ) + 3.141593 * 0.053054587352 / (12484 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001209371818 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053054587352)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405107812) : PiBarMP 12484 12 0.011 xi bn ≤ 0.162654574695 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12484 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037484767734 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.115597464982 : ℝ) ≤ √((12484 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.731821787707 : ℝ) ≤ √(12484 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12484) ≤ 0.124695078268 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037484767734 + 0.053054587352 * 1.772454 / (2 * (111.115597464982 : ℝ))) * (1 + 0.001209371818) +
        8 / (12484 * 111.731821787707) + 0.124695078268 := by gcongr
    _ ≤ (0.162654574695 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053054587352)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405107812) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283277170103) :
    parallelOracle 12484 0.011 xi bn cd ≤ 0.163663136246 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12484 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12484 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493631119 : ℝ) ≤ plow 12484 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.731821787707 : ℝ) ≤ √(12484 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283277170103 : ℝ) / (2 * 0.560493631119 * 111.731821787707)) * 0.162654574695 +
        0.283277170103 ^ 2 / (2 * 0.560493631119 * 111.731821787707) := by gcongr
    _ ≤ (0.163663136246 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053054587352) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001405107812)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283277170103) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12484 12484 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493631119 : ℝ) ≤ plow 12484 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.731821787707 : ℝ) ≤ √(12484 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12484 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12484 Θ 1.22 ≤ 0.011868601790 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.731821787707 := by gcongr <;> linarith
      _ ≤ (0.011868601790 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12484 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12484 12484 0.011 ≤ 0.008555191148 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12484 12484 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12484 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12484 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12484 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12484 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163663136246 + 0.011868601790 + (0.008555191148 : ℝ) *
        (1 + 2 * (0.283277170103 + 0.011868601790) / (0.560493631119 * 111.731821787707))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12484]

end BstLean.Part269.N12484

/-! The original eight local profiles supply actual 12484 moment certificates. -/
namespace BstLean.Part269.N12484
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12484 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12484 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12484 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053054587352 ∧
    0 ≤ bN 12484 BstLean.Part154.csC (groupTheta g) ∧ bN 12484 BstLean.Part154.csC (groupTheta g) ≤ 0.001405107812 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12484 12484 0.011
      (momentAllowance 12484 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12484 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12484 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12484 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12484 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12484 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230335814306 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12484 0.011
      (momentAllowance 12484 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12484 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12484
/-! The actual computed-centre upper energy formula at 12484. -/
namespace BstLean.Part269.N12484
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12484

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12484
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12484)
open BstLean.Part268 (cell12484)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086147442425
  | 2 => 0.087102906992
  | 3 => 0.088058467526
  | 4 => 0.089015984964
  | 5 => 0.089977694226
  | 6 => 0.090946257652
  | 7 => 0.091924823066
  | 8 => 0.092917086476
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12484 12484 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12484 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12484

/-! Actual upper energy certificates on all 43 source endpoints at 12484. -/
namespace BstLean.Part269.N12484
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12484)
open BstLean.Part268 (cell12484)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12484 (gMinus 12484) (1 - (cell12484 i).lower) ≤ 1 ∧
    energyUpper 12484 (gMinus 12484) (BstLean.Part211.gPlus 12484)
      (finiteEnergy 12484 12484 0.011) (1 - (cell12484 i).lower) ≤
      (cell12484 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨10,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨11,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨12,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨13,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨14,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨15,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨16,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨17,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨18,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨19,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨20,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨21,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨22,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨23,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨24,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨25,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨26,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨27,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨28,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨29,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨30,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨31,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨32,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨33,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨34,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨35,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨36,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨37,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨38,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨39,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨40,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨41,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨42,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨43,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨44,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨45,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨46,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨47,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨48,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨49,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨50,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨51,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12484) (by norm_num)
        (q := 1 - (cell12484 ⟨52,by decide⟩).lower)
        (by norm_num [cell12484]) (by norm_num [cell12484])
      exact ⟨E.1,E.2.trans (by norm_num [cell12484])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12484

/-! Source-cell containment and simple scalar guards at 12484. -/
namespace BstLean.Part269.N12484
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12484)
open BstLean.Part268 (cell12484)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12484 ⟨10,by decide⟩).lower ∧ (cell12484 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12484 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12484 ⟨11,by decide⟩).lower ∧ (cell12484 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12484 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12484 ⟨12,by decide⟩).lower ∧ (cell12484 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12484 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12484 ⟨13,by decide⟩).lower ∧ (cell12484 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12484 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12484 ⟨14,by decide⟩).lower ∧ (cell12484 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12484 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12484 ⟨15,by decide⟩).lower ∧ (cell12484 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12484 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12484 ⟨16,by decide⟩).lower ∧ (cell12484 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12484 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12484 ⟨17,by decide⟩).lower ∧ (cell12484 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12484 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12484 ⟨18,by decide⟩).lower ∧ (cell12484 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12484 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12484 ⟨19,by decide⟩).lower ∧ (cell12484 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12484 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12484 ⟨20,by decide⟩).lower ∧ (cell12484 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12484 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12484 ⟨21,by decide⟩).lower ∧ (cell12484 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12484 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12484 ⟨22,by decide⟩).lower ∧ (cell12484 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12484 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12484 ⟨23,by decide⟩).lower ∧ (cell12484 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12484 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12484 ⟨24,by decide⟩).lower ∧ (cell12484 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12484 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12484 ⟨25,by decide⟩).lower ∧ (cell12484 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12484 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12484 ⟨26,by decide⟩).lower ∧ (cell12484 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12484 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12484 ⟨27,by decide⟩).lower ∧ (cell12484 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12484 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12484 ⟨28,by decide⟩).lower ∧ (cell12484 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12484 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12484 ⟨29,by decide⟩).lower ∧ (cell12484 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12484 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12484 ⟨30,by decide⟩).lower ∧ (cell12484 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12484 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12484 ⟨31,by decide⟩).lower ∧ (cell12484 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12484 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12484 ⟨32,by decide⟩).lower ∧ (cell12484 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12484 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12484 ⟨33,by decide⟩).lower ∧ (cell12484 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12484 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12484 ⟨34,by decide⟩).lower ∧ (cell12484 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12484 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12484 ⟨35,by decide⟩).lower ∧ (cell12484 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12484 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12484 ⟨36,by decide⟩).lower ∧ (cell12484 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12484 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12484 ⟨37,by decide⟩).lower ∧ (cell12484 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12484 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12484 ⟨38,by decide⟩).lower ∧ (cell12484 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12484 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12484 ⟨39,by decide⟩).lower ∧ (cell12484 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12484 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12484 ⟨40,by decide⟩).lower ∧ (cell12484 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12484 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12484 ⟨41,by decide⟩).lower ∧ (cell12484 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12484 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12484 ⟨42,by decide⟩).lower ∧ (cell12484 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12484 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12484 ⟨43,by decide⟩).lower ∧ (cell12484 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12484 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12484 ⟨44,by decide⟩).lower ∧ (cell12484 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12484 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12484 ⟨45,by decide⟩).lower ∧ (cell12484 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12484 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12484 ⟨46,by decide⟩).lower ∧ (cell12484 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12484 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12484 ⟨47,by decide⟩).lower ∧ (cell12484 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12484 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12484 ⟨48,by decide⟩).lower ∧ (cell12484 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12484 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12484 ⟨49,by decide⟩).lower ∧ (cell12484 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12484 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12484 ⟨50,by decide⟩).lower ∧ (cell12484 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12484 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12484 ⟨51,by decide⟩).lower ∧ (cell12484 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12484 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12484 ⟨52,by decide⟩).lower ∧ (cell12484 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12484 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12484 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12484 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12484,cell12484,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12484 i).lower ∧
    (cell12484 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12484 i).upper ≤ (0.532 : ℝ) ∧
    (cell12484 i).centre ≤ (0.1 : ℝ) ∧ (cell12484 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12484 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12484 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12484

/-! The local source numeric instances at 12484 have no network premises. -/
namespace BstLean.Part269.N12484
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12484)
open BstLean.Part268 (cell12484)

noncomputable def sourceNumerics12484 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12484 (cell12484 i)
      scalarRow12484.M scalarRow12484.H scalarRow12484.xi := by
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
    energy_allowance := scalarRow12484.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12484]
    centre_nonneg := (scalarRow12484.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12484])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12484
/-! Actual 12485 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12485
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12485 ≤ (1.036118957693 : ℝ) := by
  have hr : (111.736296698968 : ℝ) ≤ √(12485 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.736296698968 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12485 12485 (11 / 1000) ≤
    (0.008554848520 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12485) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.736296698968 : ℝ) ≤ √(12485 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12485)
  have hdiv : K / √(12485 : ℝ) ≤ K / 111.736296698968 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.736296698968 ≤ (0.008554848520 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12485.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12485 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12485 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12485 := gPlus_lower 12485
end BstLean.Part269.N12485

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12485
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036118957692 : ℝ) ≤ wn 12485 := by
  have hn : √(12485 : ℝ) ≤ 111.736296698969 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12485 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.736296698969 ≤ 2 / √(12485 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256295042 : ℝ) ≤ rhoBar 12485 BstLean.Part154.csC ∧
    rhoBar 12485 BstLean.Part154.csC ≤ 0.000256295438 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036118957692 : ℝ) / (1.295212 * 12485) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036118957693 : ℝ) / (1.29521 * 12485) := by gcongr
      _ ≤ (0.000256295438 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12485 BstLean.Part154.csC) ≤ 0.001025247440 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12485 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12485 BstLean.Part154.csC) (piBar (rhoBar 12485 BstLean.Part154.csC)) ≤ 0.000195760344 ∧
    cc1 (rhoBar 12485 BstLean.Part154.csC) (piBar (rhoBar 12485 BstLean.Part154.csC)) ≤ 0.000124563574 ∧
    cc2 (rhoBar 12485 BstLean.Part154.csC) ≤ 0.000072310069 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12485 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12485 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12485 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12485 BstLean.Part154.csC * nuR (rhoBar 12485 BstLean.Part154.csC)) ≤ 0.000512607298 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256295438 : ℝ) * 0.001025247440 := by gcongr
      _ ≤ (0.000512607298 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12485 BstLean.Part154.csC) * nuR (rhoBar 12485 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001025247440 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12485 BstLean.Part154.csC) * rhoBar 12485 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256295438 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256295438 / 2 + 0.399 * 0.001025247440 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195760344 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512607298 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124563574 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256295438 / 1.414213562 := by gcongr
      _ ≤ (0.000072310069 : ℝ) := by norm_num

end BstLean.Part269.N12485

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12485
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12485 BstLean.Part154.csC) (piBar (rhoBar 12485 BstLean.Part154.csC)) ≤ 1.65495E-7 := by
  have hr0 : 0 ≤ rhoBar 12485 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12485 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12485 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12485 BstLean.Part154.csC) (piBar (rhoBar 12485 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12485 BstLean.Part154.csC) (piBar (rhoBar 12485 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12485 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195760344 : ℝ) ^ 2 + 0.000124563574 ^ 2 + 3 * 0.000072310069 ^ 2 +
        2 * 0.797885 * 0.000195760344 * 0.000124563574 + 2 * 0.000195760344 * 0.000072310069 +
        4 * 0.797885 * 0.000124563574 * 0.000072310069 := by gcongr
    _ ≤ (1.65495E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12485 BstLean.Part154.csC Θ ≤ 0.002676173610 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12485 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12485 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12485 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12485 BstLean.Part154.csC) (piBar (rhoBar 12485 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12485 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036118957693 * 1.65495E-7 / (0.000256295042 : ℝ) := by gcongr
    _ ≤ 0.002676173610 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12485 BstLean.Part154.csC Θ ≤ 0.002970242747 + 0.000676224188 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12485 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12485 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12485 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036118957693 : ℝ) * ((2 * Θ * 0.000256295438 +
        (6863 / 10000) * 0.000256295438 * 12485 * 0.001025247440) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002970242747 + 0.000676224188 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12485 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12485 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12485 0.011 Θ ∧ gammaRatio 12485 0.011 Θ ≤ 0.000088107744 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12485 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036118957693 : ℝ) * 0.525 / ((1 - 0.011) * 12485) := by gcongr
      _ ≤ (0.000088107744 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12485 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12485 0.011 Θ) :=
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
    badAllowance 12485 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12485 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12485 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12485 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12485 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12485 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12485 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12485 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12485 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12485 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12485 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036118957693 : ℝ) * 12485 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12485 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003787581909 + 0.003352397798 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12485

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12485
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12485 BstLean.Part154.csC) (piBar (rhoBar 12485 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12485 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12485 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12485 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12485 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12485 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12485 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12485 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12485 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12485 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12485 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12485 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12485 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12485 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12485 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052939212373 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12485) ≤ 0.010688000376 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12485 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036118957693)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010688000376 + 2 * 0.737676 / 12485) := by gcongr
    _ ≤ (0.052939212373 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12485 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12485

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12485
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493677917 : ℝ) ≤ plow 12485 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12485) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053054190753)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404991146) : eMP 12485 0.011 xi bn ≤ 0.001209273096 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12485 : ℝ) * (1 - 0.011))) ≤ 0.000597887309 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001404991146 / (12485 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597887309 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597887309 : ℝ) + 3.141593 * 0.053054190753 / (12485 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001209273096 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053054190753)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404991146) : PiBarMP 12485 12 0.011 xi bn ≤ 0.162647998140 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12485 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037483211522 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.120047696174 : ℝ) ≤ √((12485 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.736296698968 : ℝ) ≤ √(12485 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12485) ≤ 0.124690084372 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037483211522 + 0.053054190753 * 1.772454 / (2 * (111.120047696174 : ℝ))) * (1 + 0.001209273096) +
        8 / (12485 * 111.736296698968) + 0.124690084372 := by gcongr
    _ ≤ (0.162647998140 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053054190753)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404991146) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283274165763) :
    parallelOracle 12485 0.011 xi bn cd ≤ 0.163656486851 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12485 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12485 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493677917 : ℝ) ≤ plow 12485 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.736296698968 : ℝ) ≤ √(12485 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283274165763 : ℝ) / (2 * 0.560493677917 * 111.736296698968)) * 0.162647998140 +
        0.283274165763 ^ 2 / (2 * 0.560493677917 * 111.736296698968) := by gcongr
    _ ≤ (0.163656486851 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053054190753) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404991146)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283274165763) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12485 12485 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493677917 : ℝ) ≤ plow 12485 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.736296698968 : ℝ) ≤ √(12485 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12485 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12485 Θ 1.22 ≤ 0.011868126466 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.736296698968 := by gcongr <;> linarith
      _ ≤ (0.011868126466 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12485 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12485 12485 0.011 ≤ 0.008554848520 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12485 12485 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12485 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12485 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12485 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12485 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163656486851 + 0.011868126466 + (0.008554848520 : ℝ) *
        (1 + 2 * (0.283274165763 + 0.011868126466) / (0.560493677917 * 111.736296698968))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12485]

end BstLean.Part269.N12485

/-! The original eight local profiles supply actual 12485 moment certificates. -/
namespace BstLean.Part269.N12485
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12485 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12485 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12485 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053054190753 ∧
    0 ≤ bN 12485 BstLean.Part154.csC (groupTheta g) ∧ bN 12485 BstLean.Part154.csC (groupTheta g) ≤ 0.001404991146 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12485 12485 0.011
      (momentAllowance 12485 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12485 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12485 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12485 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12485 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12485 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230334953390 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12485 0.011
      (momentAllowance 12485 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12485 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12485
/-! The actual computed-centre upper energy formula at 12485. -/
namespace BstLean.Part269.N12485
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12485

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12485
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12485)
open BstLean.Part268 (cell12485)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086144264504
  | 2 => 0.087099664423
  | 3 => 0.088055149900
  | 4 => 0.089012579549
  | 5 => 0.089974185577
  | 6 => 0.090942627162
  | 7 => 0.091921048480
  | 8 => 0.092913141346
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12485 12485 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12485 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12485

/-! Actual upper energy certificates on all 43 source endpoints at 12485. -/
namespace BstLean.Part269.N12485
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12485)
open BstLean.Part268 (cell12485)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12485 (gMinus 12485) (1 - (cell12485 i).lower) ≤ 1 ∧
    energyUpper 12485 (gMinus 12485) (BstLean.Part211.gPlus 12485)
      (finiteEnergy 12485 12485 0.011) (1 - (cell12485 i).lower) ≤
      (cell12485 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨10,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨11,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨12,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨13,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨14,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨15,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨16,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨17,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨18,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨19,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨20,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨21,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨22,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨23,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨24,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨25,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨26,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨27,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨28,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨29,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨30,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨31,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨32,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨33,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨34,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨35,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨36,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨37,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨38,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨39,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨40,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨41,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨42,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨43,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨44,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨45,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨46,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨47,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨48,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨49,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨50,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨51,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12485) (by norm_num)
        (q := 1 - (cell12485 ⟨52,by decide⟩).lower)
        (by norm_num [cell12485]) (by norm_num [cell12485])
      exact ⟨E.1,E.2.trans (by norm_num [cell12485])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12485

/-! Source-cell containment and simple scalar guards at 12485. -/
namespace BstLean.Part269.N12485
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12485)
open BstLean.Part268 (cell12485)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12485 ⟨10,by decide⟩).lower ∧ (cell12485 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12485 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12485 ⟨11,by decide⟩).lower ∧ (cell12485 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12485 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12485 ⟨12,by decide⟩).lower ∧ (cell12485 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12485 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12485 ⟨13,by decide⟩).lower ∧ (cell12485 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12485 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12485 ⟨14,by decide⟩).lower ∧ (cell12485 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12485 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12485 ⟨15,by decide⟩).lower ∧ (cell12485 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12485 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12485 ⟨16,by decide⟩).lower ∧ (cell12485 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12485 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12485 ⟨17,by decide⟩).lower ∧ (cell12485 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12485 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12485 ⟨18,by decide⟩).lower ∧ (cell12485 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12485 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12485 ⟨19,by decide⟩).lower ∧ (cell12485 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12485 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12485 ⟨20,by decide⟩).lower ∧ (cell12485 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12485 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12485 ⟨21,by decide⟩).lower ∧ (cell12485 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12485 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12485 ⟨22,by decide⟩).lower ∧ (cell12485 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12485 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12485 ⟨23,by decide⟩).lower ∧ (cell12485 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12485 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12485 ⟨24,by decide⟩).lower ∧ (cell12485 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12485 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12485 ⟨25,by decide⟩).lower ∧ (cell12485 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12485 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12485 ⟨26,by decide⟩).lower ∧ (cell12485 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12485 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12485 ⟨27,by decide⟩).lower ∧ (cell12485 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12485 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12485 ⟨28,by decide⟩).lower ∧ (cell12485 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12485 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12485 ⟨29,by decide⟩).lower ∧ (cell12485 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12485 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12485 ⟨30,by decide⟩).lower ∧ (cell12485 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12485 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12485 ⟨31,by decide⟩).lower ∧ (cell12485 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12485 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12485 ⟨32,by decide⟩).lower ∧ (cell12485 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12485 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12485 ⟨33,by decide⟩).lower ∧ (cell12485 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12485 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12485 ⟨34,by decide⟩).lower ∧ (cell12485 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12485 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12485 ⟨35,by decide⟩).lower ∧ (cell12485 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12485 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12485 ⟨36,by decide⟩).lower ∧ (cell12485 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12485 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12485 ⟨37,by decide⟩).lower ∧ (cell12485 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12485 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12485 ⟨38,by decide⟩).lower ∧ (cell12485 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12485 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12485 ⟨39,by decide⟩).lower ∧ (cell12485 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12485 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12485 ⟨40,by decide⟩).lower ∧ (cell12485 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12485 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12485 ⟨41,by decide⟩).lower ∧ (cell12485 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12485 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12485 ⟨42,by decide⟩).lower ∧ (cell12485 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12485 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12485 ⟨43,by decide⟩).lower ∧ (cell12485 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12485 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12485 ⟨44,by decide⟩).lower ∧ (cell12485 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12485 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12485 ⟨45,by decide⟩).lower ∧ (cell12485 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12485 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12485 ⟨46,by decide⟩).lower ∧ (cell12485 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12485 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12485 ⟨47,by decide⟩).lower ∧ (cell12485 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12485 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12485 ⟨48,by decide⟩).lower ∧ (cell12485 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12485 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12485 ⟨49,by decide⟩).lower ∧ (cell12485 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12485 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12485 ⟨50,by decide⟩).lower ∧ (cell12485 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12485 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12485 ⟨51,by decide⟩).lower ∧ (cell12485 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12485 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12485 ⟨52,by decide⟩).lower ∧ (cell12485 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12485 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12485 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12485 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12485,cell12485,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12485 i).lower ∧
    (cell12485 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12485 i).upper ≤ (0.532 : ℝ) ∧
    (cell12485 i).centre ≤ (0.1 : ℝ) ∧ (cell12485 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12485 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12485 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12485

/-! The local source numeric instances at 12485 have no network premises. -/
namespace BstLean.Part269.N12485
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12485)
open BstLean.Part268 (cell12485)

noncomputable def sourceNumerics12485 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12485 (cell12485 i)
      scalarRow12485.M scalarRow12485.H scalarRow12485.xi := by
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
    energy_allowance := scalarRow12485.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12485]
    centre_nonneg := (scalarRow12485.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12485])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12485
/-! Actual 12486 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12486
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12486 ≤ (1.036117498457 : ℝ) := by
  have hr : (111.740771431022 : ℝ) ≤ √(12486 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.740771431022 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12486 12486 (11 / 1000) ≤
    (0.008554505932 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12486) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.740771431022 : ℝ) ≤ √(12486 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12486)
  have hdiv : K / √(12486 : ℝ) ≤ K / 111.740771431022 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.740771431022 ≤ (0.008554505932 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12486.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12486 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12486 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12486 := gPlus_lower 12486
end BstLean.Part269.N12486

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12486
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036117498456 : ℝ) ≤ wn 12486 := by
  have hn : √(12486 : ℝ) ≤ 111.740771431023 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12486 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.740771431023 ≤ 2 / √(12486 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256274154 : ℝ) ≤ rhoBar 12486 BstLean.Part154.csC ∧
    rhoBar 12486 BstLean.Part154.csC ≤ 0.000256274551 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036117498456 : ℝ) / (1.295212 * 12486) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036117498457 : ℝ) / (1.29521 * 12486) := by gcongr
      _ ≤ (0.000256274551 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12486 BstLean.Part154.csC) ≤ 0.001025163881 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12486 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12486 BstLean.Part154.csC) (piBar (rhoBar 12486 BstLean.Part154.csC)) ≤ 0.000195744390 ∧
    cc1 (rhoBar 12486 BstLean.Part154.csC) (piBar (rhoBar 12486 BstLean.Part154.csC)) ≤ 0.000124553422 ∧
    cc2 (rhoBar 12486 BstLean.Part154.csC) ≤ 0.000072304176 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12486 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12486 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12486 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12486 BstLean.Part154.csC * nuR (rhoBar 12486 BstLean.Part154.csC)) ≤ 0.000512565521 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256274551 : ℝ) * 0.001025163881 := by gcongr
      _ ≤ (0.000512565521 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12486 BstLean.Part154.csC) * nuR (rhoBar 12486 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001025163881 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12486 BstLean.Part154.csC) * rhoBar 12486 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256274551 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256274551 / 2 + 0.399 * 0.001025163881 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195744390 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512565521 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124553422 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256274551 / 1.414213562 := by gcongr
      _ ≤ (0.000072304176 : ℝ) := by norm_num

end BstLean.Part269.N12486

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12486
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12486 BstLean.Part154.csC) (piBar (rhoBar 12486 BstLean.Part154.csC)) ≤ 1.65468E-7 := by
  have hr0 : 0 ≤ rhoBar 12486 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12486 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12486 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12486 BstLean.Part154.csC) (piBar (rhoBar 12486 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12486 BstLean.Part154.csC) (piBar (rhoBar 12486 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12486 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195744390 : ℝ) ^ 2 + 0.000124553422 ^ 2 + 3 * 0.000072304176 ^ 2 +
        2 * 0.797885 * 0.000195744390 * 0.000124553422 + 2 * 0.000195744390 * 0.000072304176 +
        4 * 0.797885 * 0.000124553422 * 0.000072304176 := by gcongr
    _ ≤ (1.65468E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12486 BstLean.Part154.csC Θ ≤ 0.002675951322 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12486 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12486 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12486 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12486 BstLean.Part154.csC) (piBar (rhoBar 12486 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12486 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036117498457 * 1.65468E-7 / (0.000256274154 : ℝ) := by gcongr
    _ ≤ 0.002675951322 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12486 BstLean.Part154.csC Θ ≤ 0.002969992309 + 0.000676168126 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12486 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12486 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12486 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036117498457 : ℝ) * ((2 * Θ * 0.000256274551 +
        (6863 / 10000) * 0.000256274551 * 12486 * 0.001025163881) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002969992309 + 0.000676168126 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12486 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12486 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12486 0.011 Θ ∧ gammaRatio 12486 0.011 Θ ≤ 0.000088100564 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12486 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036117498457 : ℝ) * 0.525 / ((1 - 0.011) * 12486) := by gcongr
      _ ≤ (0.000088100564 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12486 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12486 0.011 Θ) :=
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
    badAllowance 12486 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12486 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12486 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12486 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12486 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12486 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12486 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12486 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12486 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12486 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12486 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036117498457 : ℝ) * 12486 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12486 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003787331471 + 0.003352119448 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12486

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12486
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12486 BstLean.Part154.csC) (piBar (rhoBar 12486 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12486 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12486 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12486 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12486 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12486 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12486 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12486 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12486 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12486 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12486 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12486 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12486 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12486 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12486 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052937069205 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12486) ≤ 0.010687572368 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12486 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036117498457)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010687572368 + 2 * 0.737676 / 12486) := by gcongr
    _ ≤ (0.052937069205 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12486 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12486

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12486
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493724707 : ℝ) ≤ plow 12486 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12486) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053053794182)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404874445) : eMP 12486 0.011 xi bn ≤ 0.001209174368 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12486 : ℝ) * (1 - 0.011))) ≤ 0.000597838536 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001404874445 / (12486 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597838536 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597838536 : ℝ) + 3.141593 * 0.053053794182 / (12486 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001209174368 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053053794182)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404874445) : PiBarMP 12486 12 0.011 xi bn ≤ 0.162641421657 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12486 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037481654780 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.124497749146 : ℝ) ≤ √((12486 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.740771431022 : ℝ) ≤ √(12486 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12486) ≤ 0.124685091076 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037481654780 + 0.053053794182 * 1.772454 / (2 * (111.124497749146 : ℝ))) * (1 + 0.001209174368) +
        8 / (12486 * 111.740771431022) + 0.124685091076 := by gcongr
    _ ≤ (0.162641421657 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053053794182)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404874445) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283271161736) :
    parallelOracle 12486 0.011 xi bn cd ≤ 0.163649837538 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12486 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12486 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493724707 : ℝ) ≤ plow 12486 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.740771431022 : ℝ) ≤ √(12486 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283271161736 : ℝ) / (2 * 0.560493724707 * 111.740771431022)) * 0.162641421657 +
        0.283271161736 ^ 2 / (2 * 0.560493724707 * 111.740771431022) := by gcongr
    _ ≤ (0.163649837538 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053053794182) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404874445)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283271161736) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12486 12486 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493724707 : ℝ) ≤ plow 12486 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.740771431022 : ℝ) ≤ √(12486 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12486 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12486 Θ 1.22 ≤ 0.011867651199 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.740771431022 := by gcongr <;> linarith
      _ ≤ (0.011867651199 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12486 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12486 12486 0.011 ≤ 0.008554505932 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12486 12486 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12486 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12486 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12486 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12486 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163649837538 + 0.011867651199 + (0.008554505932 : ℝ) *
        (1 + 2 * (0.283271161736 + 0.011867651199) / (0.560493724707 * 111.740771431022))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12486]

end BstLean.Part269.N12486

/-! The original eight local profiles supply actual 12486 moment certificates. -/
namespace BstLean.Part269.N12486
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12486 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12486 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12486 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053053794182 ∧
    0 ≤ bN 12486 BstLean.Part154.csC (groupTheta g) ∧ bN 12486 BstLean.Part154.csC (groupTheta g) ≤ 0.001404874445 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12486 12486 0.011
      (momentAllowance 12486 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12486 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12486 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12486 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12486 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12486 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230334092531 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12486 0.011
      (momentAllowance 12486 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12486 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12486
/-! The actual computed-centre upper energy formula at 12486. -/
namespace BstLean.Part269.N12486
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12486

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12486
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12486)
open BstLean.Part268 (cell12486)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086141087938
  | 2 => 0.087096423270
  | 3 => 0.088051833762
  | 4 => 0.089009175712
  | 5 => 0.089970678612
  | 6 => 0.090938998489
  | 7 => 0.091917275870
  | 8 => 0.092909198383
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12486 12486 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12486 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12486

/-! Actual upper energy certificates on all 43 source endpoints at 12486. -/
namespace BstLean.Part269.N12486
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12486)
open BstLean.Part268 (cell12486)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12486 (gMinus 12486) (1 - (cell12486 i).lower) ≤ 1 ∧
    energyUpper 12486 (gMinus 12486) (BstLean.Part211.gPlus 12486)
      (finiteEnergy 12486 12486 0.011) (1 - (cell12486 i).lower) ≤
      (cell12486 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨10,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨11,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨12,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨13,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨14,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨15,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨16,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨17,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨18,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨19,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨20,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨21,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨22,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨23,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨24,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨25,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨26,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨27,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨28,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨29,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨30,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨31,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨32,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨33,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨34,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨35,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨36,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨37,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨38,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨39,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨40,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨41,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨42,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨43,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨44,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨45,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨46,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨47,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨48,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨49,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨50,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨51,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12486) (by norm_num)
        (q := 1 - (cell12486 ⟨52,by decide⟩).lower)
        (by norm_num [cell12486]) (by norm_num [cell12486])
      exact ⟨E.1,E.2.trans (by norm_num [cell12486])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12486

/-! Source-cell containment and simple scalar guards at 12486. -/
namespace BstLean.Part269.N12486
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12486)
open BstLean.Part268 (cell12486)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12486 ⟨10,by decide⟩).lower ∧ (cell12486 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12486 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12486 ⟨11,by decide⟩).lower ∧ (cell12486 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12486 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12486 ⟨12,by decide⟩).lower ∧ (cell12486 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12486 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12486 ⟨13,by decide⟩).lower ∧ (cell12486 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12486 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12486 ⟨14,by decide⟩).lower ∧ (cell12486 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12486 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12486 ⟨15,by decide⟩).lower ∧ (cell12486 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12486 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12486 ⟨16,by decide⟩).lower ∧ (cell12486 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12486 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12486 ⟨17,by decide⟩).lower ∧ (cell12486 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12486 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12486 ⟨18,by decide⟩).lower ∧ (cell12486 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12486 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12486 ⟨19,by decide⟩).lower ∧ (cell12486 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12486 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12486 ⟨20,by decide⟩).lower ∧ (cell12486 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12486 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12486 ⟨21,by decide⟩).lower ∧ (cell12486 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12486 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12486 ⟨22,by decide⟩).lower ∧ (cell12486 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12486 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12486 ⟨23,by decide⟩).lower ∧ (cell12486 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12486 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12486 ⟨24,by decide⟩).lower ∧ (cell12486 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12486 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12486 ⟨25,by decide⟩).lower ∧ (cell12486 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12486 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12486 ⟨26,by decide⟩).lower ∧ (cell12486 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12486 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12486 ⟨27,by decide⟩).lower ∧ (cell12486 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12486 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12486 ⟨28,by decide⟩).lower ∧ (cell12486 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12486 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12486 ⟨29,by decide⟩).lower ∧ (cell12486 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12486 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12486 ⟨30,by decide⟩).lower ∧ (cell12486 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12486 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12486 ⟨31,by decide⟩).lower ∧ (cell12486 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12486 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12486 ⟨32,by decide⟩).lower ∧ (cell12486 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12486 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12486 ⟨33,by decide⟩).lower ∧ (cell12486 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12486 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12486 ⟨34,by decide⟩).lower ∧ (cell12486 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12486 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12486 ⟨35,by decide⟩).lower ∧ (cell12486 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12486 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12486 ⟨36,by decide⟩).lower ∧ (cell12486 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12486 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12486 ⟨37,by decide⟩).lower ∧ (cell12486 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12486 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12486 ⟨38,by decide⟩).lower ∧ (cell12486 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12486 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12486 ⟨39,by decide⟩).lower ∧ (cell12486 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12486 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12486 ⟨40,by decide⟩).lower ∧ (cell12486 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12486 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12486 ⟨41,by decide⟩).lower ∧ (cell12486 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12486 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12486 ⟨42,by decide⟩).lower ∧ (cell12486 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12486 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12486 ⟨43,by decide⟩).lower ∧ (cell12486 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12486 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12486 ⟨44,by decide⟩).lower ∧ (cell12486 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12486 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12486 ⟨45,by decide⟩).lower ∧ (cell12486 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12486 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12486 ⟨46,by decide⟩).lower ∧ (cell12486 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12486 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12486 ⟨47,by decide⟩).lower ∧ (cell12486 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12486 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12486 ⟨48,by decide⟩).lower ∧ (cell12486 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12486 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12486 ⟨49,by decide⟩).lower ∧ (cell12486 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12486 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12486 ⟨50,by decide⟩).lower ∧ (cell12486 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12486 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12486 ⟨51,by decide⟩).lower ∧ (cell12486 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12486 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12486 ⟨52,by decide⟩).lower ∧ (cell12486 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12486 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12486 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12486 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12486,cell12486,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12486 i).lower ∧
    (cell12486 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12486 i).upper ≤ (0.532 : ℝ) ∧
    (cell12486 i).centre ≤ (0.1 : ℝ) ∧ (cell12486 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12486 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12486 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12486

/-! The local source numeric instances at 12486 have no network premises. -/
namespace BstLean.Part269.N12486
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12486)
open BstLean.Part268 (cell12486)

noncomputable def sourceNumerics12486 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12486 (cell12486 i)
      scalarRow12486.M scalarRow12486.H scalarRow12486.xi := by
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
    energy_allowance := scalarRow12486.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12486]
    centre_nonneg := (scalarRow12486.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12486])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12486
/-! Actual 12487 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N12487
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 12487 ≤ (1.036116039396 : ℝ) := by
  have hr : (111.745245983889 : ℝ) ≤ √(12487 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (111.745245983889 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 12487 12487 (11 / 1000) ≤
    (0.008554163386 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 12487) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (111.745245983889 : ℝ) ≤ √(12487 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 12487)
  have hdiv : K / √(12487 : ℝ) ≤ K / 111.745245983889 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 111.745245983889 ≤ (0.008554163386 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow12487.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 12487 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 12487 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 12487 := gPlus_lower 12487
end BstLean.Part269.N12487

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N12487
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.036116039395 : ℝ) ≤ wn 12487 := by
  have hn : √(12487 : ℝ) ≤ 111.745245983890 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(12487 : ℝ) := by positivity
  have hd : (2 : ℝ) / 111.745245983890 ≤ 2 / √(12487 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000256253270 : ℝ) ≤ rhoBar 12487 BstLean.Part154.csC ∧
    rhoBar 12487 BstLean.Part154.csC ≤ 0.000256253667 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.036116039395 : ℝ) / (1.295212 * 12487) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.036116039396 : ℝ) / (1.29521 * 12487) := by gcongr
      _ ≤ (0.000256253667 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 12487 BstLean.Part154.csC) ≤ 0.001025080334 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 12487 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 12487 BstLean.Part154.csC) (piBar (rhoBar 12487 BstLean.Part154.csC)) ≤ 0.000195728438 ∧
    cc1 (rhoBar 12487 BstLean.Part154.csC) (piBar (rhoBar 12487 BstLean.Part154.csC)) ≤ 0.000124543272 ∧
    cc2 (rhoBar 12487 BstLean.Part154.csC) ≤ 0.000072298284 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 12487 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 12487 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 12487 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 12487 BstLean.Part154.csC * nuR (rhoBar 12487 BstLean.Part154.csC)) ≤ 0.000512523751 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000256253667 : ℝ) * 0.001025080334 := by gcongr
      _ ≤ (0.000512523751 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 12487 BstLean.Part154.csC) * nuR (rhoBar 12487 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.001025080334 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 12487 BstLean.Part154.csC) * rhoBar 12487 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000256253667 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000256253667 / 2 + 0.399 * 0.001025080334 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000195728438 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000512523751 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000124543272 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000256253667 / 1.414213562 := by gcongr
      _ ≤ (0.000072298284 : ℝ) := by norm_num

end BstLean.Part269.N12487

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N12487
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 12487 BstLean.Part154.csC) (piBar (rhoBar 12487 BstLean.Part154.csC)) ≤ 1.65441E-7 := by
  have hr0 : 0 ≤ rhoBar 12487 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 12487 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12487 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 12487 BstLean.Part154.csC) (piBar (rhoBar 12487 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 12487 BstLean.Part154.csC) (piBar (rhoBar 12487 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 12487 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000195728438 : ℝ) ^ 2 + 0.000124543272 ^ 2 + 3 * 0.000072298284 ^ 2 +
        2 * 0.797885 * 0.000195728438 * 0.000124543272 + 2 * 0.000195728438 * 0.000072298284 +
        4 * 0.797885 * 0.000124543272 * 0.000072298284 := by gcongr
    _ ≤ (1.65441E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 12487 BstLean.Part154.csC Θ ≤ 0.002675728957 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 12487 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 12487 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 12487 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 12487 BstLean.Part154.csC) (piBar (rhoBar 12487 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 12487 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.036116039396 * 1.65441E-7 / (0.000256253270 : ℝ) := by gcongr
    _ ≤ 0.002675728957 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 12487 BstLean.Part154.csC Θ ≤ 0.002969741904 + 0.000676112072 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 12487 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 12487 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 12487 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.036116039396 : ℝ) * ((2 * Θ * 0.000256253667 +
        (6863 / 10000) * 0.000256253667 * 12487 * 0.001025080334) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002969741904 + 0.000676112072 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 12487 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 12487 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 12487 0.011 Θ ∧ gammaRatio 12487 0.011 Θ ≤ 0.000088093384 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 12487 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.036116039396 : ℝ) * 0.525 / ((1 - 0.011) * 12487) := by gcongr
      _ ≤ (0.000088093384 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 12487 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 12487 0.011 Θ) :=
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
    badAllowance 12487 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000817339162 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 12487 BstLean.Part154.csC) 1.22 ≤ 3.0670E-8 := by
    have he : (17.3 : ℝ) ≤ gap 2 (rhoBar 12487 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 12487 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 12487 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 12487 0.011 Θ) 1.12 ≤ 3.7460E-8 := by
    have he : (17.1 : ℝ) ≤ gap 1 (gammaRatio 12487 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 12487 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 12487 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_17_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 12487 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 12487 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.036116039396 : ℝ) * 12487 *
        (3.0670E-8 / 1.1045361 + 3.7460E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000817339162 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 12487 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003787081066 + 0.003351841029 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N12487

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N12487
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 12487 BstLean.Part154.csC) (piBar (rhoBar 12487 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 12487 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 12487 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12487 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 12487 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 12487 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12487 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 12487 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 12487 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 12487 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 12487 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 12487 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 12487 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 12487 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 12487 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.052934926295 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 12487) ≤ 0.010687144411 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 12487 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.036116039396)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010687144411 + 2 * 0.737676 / 12487) := by gcongr
    _ ≤ (0.052934926295 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 12487 12 ≤ 0.0015 := by
  exact BstLean.Part269.S5.uniform_n22_upper (by norm_num)

end BstLean.Part269.N12487

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N12487
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560493771490 : ℝ) ≤ plow 12487 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 12487) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053053397607)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404757703) : eMP 12487 0.011 xi bn ≤ 0.001209075630 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((12487 : ℝ) * (1 - 0.011))) ≤ 0.000597789758 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001404757703 / (12487 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000597789758 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000597789758 : ℝ) + 3.141593 * 0.053053397607 / (12487 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001209075630 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053053397607)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404757703) : PiBarMP 12487 12 0.011 xi bn ≤ 0.162634845163 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 12487 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.037480097426 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (111.128947623920 : ℝ) ≤ √((12487 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (111.745245983889 : ℝ) ≤ √(12487 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 12487) ≤ 0.124680098380 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.037480097426 + 0.053053397607 * 1.772454 / (2 * (111.128947623920 : ℝ))) * (1 + 0.001209075630) +
        8 / (12487 * 111.745245983889) + 0.124680098380 := by gcongr
    _ ≤ (0.162634845163 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053053397607)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404757703) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283268157956) :
    parallelOracle 12487 0.011 xi bn cd ≤ 0.163643188223 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 12487 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 12487 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560493771490 : ℝ) ≤ plow 12487 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.745245983889 : ℝ) ≤ √(12487 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.283268157956 : ℝ) / (2 * 0.560493771490 * 111.745245983889)) * 0.162634845163 +
        0.283268157956 ^ 2 / (2 * 0.560493771490 * 111.745245983889) := by gcongr
    _ ≤ (0.163643188223 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.053053397607) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001404757703)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.283268157956) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 12487 12487 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560493771490 : ℝ) ≤ plow 12487 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (111.745245983889 : ℝ) ≤ √(12487 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 12487 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 12487 Θ 1.22 ≤ 0.011867175989 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 111.745245983889 := by gcongr <;> linarith
      _ ≤ (0.011867175989 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 12487 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 12487 12487 0.011 ≤ 0.008554163386 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 12487 12487 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 12487 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 12487 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 12487 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 12487 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.163643188223 + 0.011867175989 + (0.008554163386 : ℝ) *
        (1 + 2 * (0.283268157956 + 0.011867175989) / (0.560493771490 * 111.745245983889))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow12487]

end BstLean.Part269.N12487

/-! The original eight local profiles supply actual 12487 moment certificates. -/
namespace BstLean.Part269.N12487
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 12487 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 12487 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 12487 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.053053397607 ∧
    0 ≤ bN 12487 BstLean.Part154.csC (groupTheta g) ∧ bN 12487 BstLean.Part154.csC (groupTheta g) ≤ 0.001404757703 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 12487 12487 0.011
      (momentAllowance 12487 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12487 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 12487 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 12487 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 12487 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 12487 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.230333231661 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 12487 0.011
      (momentAllowance 12487 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 12487 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N12487
/-! The actual computed-centre upper energy formula at 12487. -/
namespace BstLean.Part269.N12487
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N12487

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N12487
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12487)
open BstLean.Part268 (cell12487)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.086137912728
  | 2 => 0.087093183530
  | 3 => 0.088048519109
  | 4 => 0.089005773449
  | 5 => 0.089967173332
  | 6 => 0.090935371631
  | 7 => 0.091913505235
  | 8 => 0.092905257585
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 12487 12487 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 12487 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003790088722 + 0.003355178034 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S5.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S5.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N12487

/-! Actual upper energy certificates on all 43 source endpoints at 12487. -/
namespace BstLean.Part269.N12487
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow12487)
open BstLean.Part268 (cell12487)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 12487 (gMinus 12487) (1 - (cell12487 i).lower) ≤ 1 ∧
    energyUpper 12487 (gMinus 12487) (BstLean.Part211.gPlus 12487)
      (finiteEnergy 12487 12487 0.011) (1 - (cell12487 i).lower) ≤
      (cell12487 i).energy := by
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
      have E := BstLean.Part269.S5.uniformEnergy10 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨10,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy11 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨11,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy12 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨12,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy13 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨13,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy14 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨14,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy15 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨15,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy16 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨16,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy17 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨17,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy18 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨18,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy19 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨19,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy20 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨20,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy21 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨21,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy22 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨22,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy23 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨23,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy24 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨24,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy25 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨25,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy26 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨26,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy27 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨27,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy28 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨28,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy29 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨29,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy30 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨30,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy31 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨31,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy32 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨32,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy33 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨33,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy34 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨34,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy35 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨35,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy36 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨36,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy37 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨37,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy38 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨38,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy39 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨39,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy40 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨40,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy41 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨41,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy42 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨42,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy43 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨43,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy44 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨44,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy45 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨45,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy46 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨46,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy47 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨47,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy48 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨48,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy49 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨49,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy50 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨50,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy51 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨51,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S5.uniformEnergy52 (n := 12487) (by norm_num)
        (q := 1 - (cell12487 ⟨52,by decide⟩).lower)
        (by norm_num [cell12487]) (by norm_num [cell12487])
      exact ⟨E.1,E.2.trans (by norm_num [cell12487])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N12487

/-! Source-cell containment and simple scalar guards at 12487. -/
namespace BstLean.Part269.N12487
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12487)
open BstLean.Part268 (cell12487)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell12487 ⟨10,by decide⟩).lower ∧ (cell12487 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell12487 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell12487 ⟨11,by decide⟩).lower ∧ (cell12487 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell12487 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell12487 ⟨12,by decide⟩).lower ∧ (cell12487 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell12487 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell12487 ⟨13,by decide⟩).lower ∧ (cell12487 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell12487 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell12487 ⟨14,by decide⟩).lower ∧ (cell12487 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell12487 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell12487 ⟨15,by decide⟩).lower ∧ (cell12487 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell12487 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell12487 ⟨16,by decide⟩).lower ∧ (cell12487 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell12487 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell12487 ⟨17,by decide⟩).lower ∧ (cell12487 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell12487 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell12487 ⟨18,by decide⟩).lower ∧ (cell12487 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell12487 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell12487 ⟨19,by decide⟩).lower ∧ (cell12487 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell12487 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell12487 ⟨20,by decide⟩).lower ∧ (cell12487 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell12487 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell12487 ⟨21,by decide⟩).lower ∧ (cell12487 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell12487 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell12487 ⟨22,by decide⟩).lower ∧ (cell12487 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell12487 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell12487 ⟨23,by decide⟩).lower ∧ (cell12487 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell12487 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell12487 ⟨24,by decide⟩).lower ∧ (cell12487 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell12487 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell12487 ⟨25,by decide⟩).lower ∧ (cell12487 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell12487 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell12487 ⟨26,by decide⟩).lower ∧ (cell12487 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell12487 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell12487 ⟨27,by decide⟩).lower ∧ (cell12487 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell12487 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell12487 ⟨28,by decide⟩).lower ∧ (cell12487 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell12487 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell12487 ⟨29,by decide⟩).lower ∧ (cell12487 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell12487 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell12487 ⟨30,by decide⟩).lower ∧ (cell12487 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell12487 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell12487 ⟨31,by decide⟩).lower ∧ (cell12487 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell12487 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell12487 ⟨32,by decide⟩).lower ∧ (cell12487 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell12487 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell12487 ⟨33,by decide⟩).lower ∧ (cell12487 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell12487 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell12487 ⟨34,by decide⟩).lower ∧ (cell12487 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell12487 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell12487 ⟨35,by decide⟩).lower ∧ (cell12487 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell12487 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell12487 ⟨36,by decide⟩).lower ∧ (cell12487 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell12487 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell12487 ⟨37,by decide⟩).lower ∧ (cell12487 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell12487 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell12487 ⟨38,by decide⟩).lower ∧ (cell12487 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell12487 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell12487 ⟨39,by decide⟩).lower ∧ (cell12487 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell12487 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell12487 ⟨40,by decide⟩).lower ∧ (cell12487 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell12487 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell12487 ⟨41,by decide⟩).lower ∧ (cell12487 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell12487 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell12487 ⟨42,by decide⟩).lower ∧ (cell12487 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell12487 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell12487 ⟨43,by decide⟩).lower ∧ (cell12487 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell12487 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell12487 ⟨44,by decide⟩).lower ∧ (cell12487 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell12487 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell12487 ⟨45,by decide⟩).lower ∧ (cell12487 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell12487 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell12487 ⟨46,by decide⟩).lower ∧ (cell12487 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell12487 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell12487 ⟨47,by decide⟩).lower ∧ (cell12487 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell12487 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell12487 ⟨48,by decide⟩).lower ∧ (cell12487 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell12487 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell12487 ⟨49,by decide⟩).lower ∧ (cell12487 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell12487 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell12487 ⟨50,by decide⟩).lower ∧ (cell12487 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell12487 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell12487 ⟨51,by decide⟩).lower ∧ (cell12487 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell12487 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell12487 ⟨52,by decide⟩).lower ∧ (cell12487 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell12487 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell12487 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell12487 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow12487,cell12487,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell12487 i).lower ∧
    (cell12487 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell12487 i).upper ≤ (0.532 : ℝ) ∧
    (cell12487 i).centre ≤ (0.1 : ℝ) ∧ (cell12487 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell12487 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell12487 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N12487

/-! The local source numeric instances at 12487 have no network premises. -/
namespace BstLean.Part269.N12487
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow12487)
open BstLean.Part268 (cell12487)

noncomputable def sourceNumerics12487 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 12487 (cell12487 i)
      scalarRow12487.M scalarRow12487.H scalarRow12487.xi := by
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
    energy_allowance := scalarRow12487.energy_allowance
    parallel_nonneg := by norm_num [scalarRow12487]
    centre_nonneg := (scalarRow12487.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D5.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow12487])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N12487