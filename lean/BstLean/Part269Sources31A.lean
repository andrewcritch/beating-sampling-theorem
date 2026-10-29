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
import BstLean.Part269Direction31
import BstLean.Part269Shared31
import BstLean.Part269Finite
import BstLean.Part269Rows31
import BstLean.Part269Source
/-! Actual 13125 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13125
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13125 ≤ (1.035219624343 : ℝ) := by
  have hr : (114.564392373896 : ℝ) ≤ √(13125 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.564392373896 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13125 13125 (11 / 1000) ≤
    (0.008343664993 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13125) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.564392373896 : ℝ) ≤ √(13125 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13125)
  have hdiv : K / √(13125 : ℝ) ≤ K / 114.564392373896 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.564392373896 ≤ (0.008343664993 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13125.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13125 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13125 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13125 := gPlus_lower 13125
end BstLean.Part269.N13125

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13125
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035219624342 : ℝ) ≤ wn 13125 := by
  have hn : √(13125 : ℝ) ≤ 114.564392373897 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13125 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.564392373897 ≤ 2 / √(13125 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243585995 : ℝ) ≤ rhoBar 13125 BstLean.Part154.csC ∧
    rhoBar 13125 BstLean.Part154.csC ≤ 0.000243586372 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035219624342 : ℝ) / (1.295212 * 13125) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035219624343 : ℝ) / (1.29521 * 13125) := by gcongr
      _ ≤ (0.000243586372 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13125 BstLean.Part154.csC) ≤ 0.000974404823 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13125 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13125 BstLean.Part154.csC) (piBar (rhoBar 13125 BstLean.Part154.csC)) ≤ 0.000186052629 ∧
    cc1 (rhoBar 13125 BstLean.Part154.csC) (piBar (rhoBar 13125 BstLean.Part154.csC)) ≤ 0.000118386582 ∧
    cc2 (rhoBar 13125 BstLean.Part154.csC) ≤ 0.000068724389 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13125 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13125 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13125 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13125 BstLean.Part154.csC * nuR (rhoBar 13125 BstLean.Part154.csC)) ≤ 0.000487187578 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243586372 : ℝ) * 0.000974404823 := by gcongr
      _ ≤ (0.000487187578 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13125 BstLean.Part154.csC) * nuR (rhoBar 13125 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000974404823 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13125 BstLean.Part154.csC) * rhoBar 13125 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243586372 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243586372 / 2 + 0.399 * 0.000974404823 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186052629 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487187578 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118386582 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243586372 / 1.414213562 := by gcongr
      _ ≤ (0.000068724389 : ℝ) := by norm_num

end BstLean.Part269.N13125

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13125
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13125 BstLean.Part154.csC) (piBar (rhoBar 13125 BstLean.Part154.csC)) ≤ 1.49488E-7 := by
  have hr0 : 0 ≤ rhoBar 13125 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13125 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13125 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13125 BstLean.Part154.csC) (piBar (rhoBar 13125 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13125 BstLean.Part154.csC) (piBar (rhoBar 13125 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13125 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186052629 : ℝ) ^ 2 + 0.000118386582 ^ 2 + 3 * 0.000068724389 ^ 2 +
        2 * 0.797885 * 0.000186052629 * 0.000118386582 + 2 * 0.000186052629 * 0.000068724389 +
        4 * 0.797885 * 0.000118386582 * 0.000068724389 := by gcongr
    _ ≤ (1.49488E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13125 BstLean.Part154.csC Θ ≤ 0.002541244807 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13125 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13125 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13125 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13125 BstLean.Part154.csC) (piBar (rhoBar 13125 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13125 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035219624343 * 1.49488E-7 / (0.000243585995 : ℝ) := by gcongr
    _ ≤ 0.002541244807 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13125 BstLean.Part154.csC Θ ≤ 0.002818048272 + 0.000642134033 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13125 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13125 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13125 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035219624343 : ℝ) * ((2 * Θ * 0.000243586372 +
        (6863 / 10000) * 0.000243586372 * 13125 * 0.000974404823) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002818048272 + 0.000642134033 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13125 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13125 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13125 0.011 Θ ∧ gammaRatio 13125 0.011 Θ ≤ 0.000083738696 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13125 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035219624343 : ℝ) * 0.525 / ((1 - 0.011) * 13125) := by gcongr
      _ ≤ (0.000083738696 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13125 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13125 0.011 Θ) :=
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
    badAllowance 13125 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13125 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13125 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13125 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13125 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13125 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13125 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13125 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13125 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13125 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13125 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035219624343 : ℝ) * 13125 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13125 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003167136758 + 0.003183378840 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13125

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13125
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13125 BstLean.Part154.csC) (piBar (rhoBar 13125 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13125 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13125 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13125 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13125 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13125 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13125 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13125 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13125 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13125 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13125 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13125 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13125 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13125 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13125 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051618435840 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13125) ≤ 0.010424160216 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13125 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035219624343)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010424160216 + 2 * 0.737676 / 13125) := by gcongr
    _ ≤ (0.051618435840 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13125 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13125

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13125
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522165699 : ℝ) ≤ plow 13125 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13125) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345010649)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334153524) : eMP 13125 0.011 xi bn ≤ 0.001149144079 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13125 : ℝ) * (1 - 0.011))) ≤ 0.000568237725 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001334153524 / (13125 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568237725 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568237725 : ℝ) + 3.141593 * 0.052345010649 / (13125 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001149144079 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345010649)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334153524) : PiBarMP 13125 12 0.011 xi bn ≤ 0.158593024714 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13125 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036526066364 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.932545833049 : ℝ) ≤ √((13125 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.564392373896 : ℝ) ≤ √(13125 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13125) ≤ 0.121612029481 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036526066364 + 0.052345010649 * 1.772454 / (2 * (113.932545833049 : ℝ))) * (1 + 0.001149144079) +
        8 / (13125 * 114.564392373896) + 0.121612029481 := by gcongr
    _ ≤ (0.158593024714 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345010649)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334153524) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280408756110) :
    parallelOracle 13125 0.011 xi bn cd ≤ 0.159551509911 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13125 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13125 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522165699 : ℝ) ≤ plow 13125 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.564392373896 : ℝ) ≤ √(13125 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280408756110 : ℝ) / (2 * 0.560522165699 * 114.564392373896)) * 0.158593024714 +
        0.280408756110 ^ 2 / (2 * 0.560522165699 * 114.564392373896) := by gcongr
    _ ≤ (0.159551509911 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052345010649) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334153524)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280408756110) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13125 13125 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522165699 : ℝ) ≤ plow 13125 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.564392373896 : ℝ) ≤ √(13125 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13125 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13125 Θ 1.22 ≤ 0.011575154135 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.564392373896 := by gcongr <;> linarith
      _ ≤ (0.011575154135 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13125 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13125 13125 0.011 ≤ 0.008343664993 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13125 13125 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13125 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13125 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13125 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13125 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159551509911 + 0.011575154135 + (0.008343664993 : ℝ) *
        (1 + 2 * (0.280408756110 + 0.011575154135) / (0.560522165699 * 114.564392373896))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13125]

end BstLean.Part269.N13125

/-! The original eight local profiles supply actual 13125 moment certificates. -/
namespace BstLean.Part269.N13125
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13125 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13125 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13125 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052345010649 ∧
    0 ≤ bN 13125 BstLean.Part154.csC (groupTheta g) ∧ bN 13125 BstLean.Part154.csC (groupTheta g) ≤ 0.001334153524 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13125 13125 0.011
      (momentAllowance 13125 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13125 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13125 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13125 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13125 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13125 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228790320270 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13125 0.011
      (momentAllowance 13125 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13125 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13125
/-! The actual computed-centre upper energy formula at 13125. -/
namespace BstLean.Part269.N13125
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13125

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13125
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13125)
open BstLean.Part268 (cell13125)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084338863501
  | 2 => 0.085263428023
  | 3 => 0.086183595103
  | 4 => 0.087100185814
  | 5 => 0.088014210284
  | 6 => 0.088926897841
  | 7 => 0.089839730398
  | 8 => 0.090754479187
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13125 13125 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13125 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13125

/-! Actual upper energy certificates on all 43 source endpoints at 13125. -/
namespace BstLean.Part269.N13125
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13125)
open BstLean.Part268 (cell13125)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13125 (gMinus 13125) (1 - (cell13125 i).lower) ≤ 1 ∧
    energyUpper 13125 (gMinus 13125) (BstLean.Part211.gPlus 13125)
      (finiteEnergy 13125 13125 0.011) (1 - (cell13125 i).lower) ≤
      (cell13125 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨10,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨11,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨12,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨13,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨14,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨15,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨16,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨17,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨18,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨19,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨20,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨21,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨22,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨23,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨24,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨25,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨26,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨27,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨28,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨29,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨30,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨31,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨32,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨33,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨34,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨35,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨36,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨37,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨38,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨39,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨40,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨41,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨42,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨43,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨44,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨45,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨46,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨47,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨48,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨49,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨50,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨51,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13125) (by norm_num)
        (q := 1 - (cell13125 ⟨52,by decide⟩).lower)
        (by norm_num [cell13125]) (by norm_num [cell13125])
      exact ⟨E.1,E.2.trans (by norm_num [cell13125])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13125

/-! Source-cell containment and simple scalar guards at 13125. -/
namespace BstLean.Part269.N13125
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13125)
open BstLean.Part268 (cell13125)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13125 ⟨10,by decide⟩).lower ∧ (cell13125 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13125 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13125 ⟨11,by decide⟩).lower ∧ (cell13125 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13125 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13125 ⟨12,by decide⟩).lower ∧ (cell13125 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13125 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13125 ⟨13,by decide⟩).lower ∧ (cell13125 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13125 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13125 ⟨14,by decide⟩).lower ∧ (cell13125 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13125 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13125 ⟨15,by decide⟩).lower ∧ (cell13125 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13125 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13125 ⟨16,by decide⟩).lower ∧ (cell13125 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13125 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13125 ⟨17,by decide⟩).lower ∧ (cell13125 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13125 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13125 ⟨18,by decide⟩).lower ∧ (cell13125 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13125 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13125 ⟨19,by decide⟩).lower ∧ (cell13125 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13125 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13125 ⟨20,by decide⟩).lower ∧ (cell13125 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13125 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13125 ⟨21,by decide⟩).lower ∧ (cell13125 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13125 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13125 ⟨22,by decide⟩).lower ∧ (cell13125 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13125 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13125 ⟨23,by decide⟩).lower ∧ (cell13125 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13125 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13125 ⟨24,by decide⟩).lower ∧ (cell13125 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13125 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13125 ⟨25,by decide⟩).lower ∧ (cell13125 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13125 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13125 ⟨26,by decide⟩).lower ∧ (cell13125 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13125 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13125 ⟨27,by decide⟩).lower ∧ (cell13125 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13125 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13125 ⟨28,by decide⟩).lower ∧ (cell13125 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13125 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13125 ⟨29,by decide⟩).lower ∧ (cell13125 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13125 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13125 ⟨30,by decide⟩).lower ∧ (cell13125 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13125 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13125 ⟨31,by decide⟩).lower ∧ (cell13125 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13125 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13125 ⟨32,by decide⟩).lower ∧ (cell13125 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13125 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13125 ⟨33,by decide⟩).lower ∧ (cell13125 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13125 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13125 ⟨34,by decide⟩).lower ∧ (cell13125 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13125 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13125 ⟨35,by decide⟩).lower ∧ (cell13125 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13125 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13125 ⟨36,by decide⟩).lower ∧ (cell13125 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13125 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13125 ⟨37,by decide⟩).lower ∧ (cell13125 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13125 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13125 ⟨38,by decide⟩).lower ∧ (cell13125 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13125 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13125 ⟨39,by decide⟩).lower ∧ (cell13125 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13125 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13125 ⟨40,by decide⟩).lower ∧ (cell13125 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13125 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13125 ⟨41,by decide⟩).lower ∧ (cell13125 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13125 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13125 ⟨42,by decide⟩).lower ∧ (cell13125 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13125 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13125 ⟨43,by decide⟩).lower ∧ (cell13125 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13125 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13125 ⟨44,by decide⟩).lower ∧ (cell13125 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13125 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13125 ⟨45,by decide⟩).lower ∧ (cell13125 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13125 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13125 ⟨46,by decide⟩).lower ∧ (cell13125 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13125 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13125 ⟨47,by decide⟩).lower ∧ (cell13125 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13125 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13125 ⟨48,by decide⟩).lower ∧ (cell13125 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13125 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13125 ⟨49,by decide⟩).lower ∧ (cell13125 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13125 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13125 ⟨50,by decide⟩).lower ∧ (cell13125 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13125 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13125 ⟨51,by decide⟩).lower ∧ (cell13125 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13125 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13125 ⟨52,by decide⟩).lower ∧ (cell13125 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13125 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13125 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13125 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13125,cell13125,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13125 i).lower ∧
    (cell13125 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13125 i).upper ≤ (0.532 : ℝ) ∧
    (cell13125 i).centre ≤ (0.1 : ℝ) ∧ (cell13125 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13125 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13125 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13125

/-! The local source numeric instances at 13125 have no network premises. -/
namespace BstLean.Part269.N13125
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13125)
open BstLean.Part268 (cell13125)

noncomputable def sourceNumerics13125 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13125 (cell13125 i)
      scalarRow13125.M scalarRow13125.H scalarRow13125.xi := by
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
    energy_allowance := scalarRow13125.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13125]
    centre_nonneg := (scalarRow13125.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13125])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13125
/-! Actual 13126 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13126
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13126 ≤ (1.035218271111 : ℝ) := by
  have hr : (114.568756648573 : ℝ) ≤ √(13126 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.568756648573 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13126 13126 (11 / 1000) ≤
    (0.008343347155 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13126) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.568756648573 : ℝ) ≤ √(13126 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13126)
  have hdiv : K / √(13126 : ℝ) ≤ K / 114.568756648573 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.568756648573 ≤ (0.008343347155 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13126.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13126 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13126 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13126 := gPlus_lower 13126
end BstLean.Part269.N13126

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13126
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035218271110 : ℝ) ≤ wn 13126 := by
  have hn : √(13126 : ℝ) ≤ 114.568756648574 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13126 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.568756648574 ≤ 2 / √(13126 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243567119 : ℝ) ≤ rhoBar 13126 BstLean.Part154.csC ∧
    rhoBar 13126 BstLean.Part154.csC ≤ 0.000243567496 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035218271110 : ℝ) / (1.295212 * 13126) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035218271111 : ℝ) / (1.29521 * 13126) := by gcongr
      _ ≤ (0.000243567496 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13126 BstLean.Part154.csC) ≤ 0.000974329310 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13126 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13126 BstLean.Part154.csC) (piBar (rhoBar 13126 BstLean.Part154.csC)) ≤ 0.000186038211 ∧
    cc1 (rhoBar 13126 BstLean.Part154.csC) (piBar (rhoBar 13126 BstLean.Part154.csC)) ≤ 0.000118377408 ∧
    cc2 (rhoBar 13126 BstLean.Part154.csC) ≤ 0.000068719064 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13126 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13126 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13126 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13126 BstLean.Part154.csC * nuR (rhoBar 13126 BstLean.Part154.csC)) ≤ 0.000487149824 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243567496 : ℝ) * 0.000974329310 := by gcongr
      _ ≤ (0.000487149824 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13126 BstLean.Part154.csC) * nuR (rhoBar 13126 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000974329310 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13126 BstLean.Part154.csC) * rhoBar 13126 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243567496 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243567496 / 2 + 0.399 * 0.000974329310 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186038211 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487149824 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118377408 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243567496 / 1.414213562 := by gcongr
      _ ≤ (0.000068719064 : ℝ) := by norm_num

end BstLean.Part269.N13126

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13126
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13126 BstLean.Part154.csC) (piBar (rhoBar 13126 BstLean.Part154.csC)) ≤ 1.49465E-7 := by
  have hr0 : 0 ≤ rhoBar 13126 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13126 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13126 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13126 BstLean.Part154.csC) (piBar (rhoBar 13126 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13126 BstLean.Part154.csC) (piBar (rhoBar 13126 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13126 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186038211 : ℝ) ^ 2 + 0.000118377408 ^ 2 + 3 * 0.000068719064 ^ 2 +
        2 * 0.797885 * 0.000186038211 * 0.000118377408 + 2 * 0.000186038211 * 0.000068719064 +
        4 * 0.797885 * 0.000118377408 * 0.000068719064 := by gcongr
    _ ≤ (1.49465E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13126 BstLean.Part154.csC Θ ≤ 0.002541047405 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13126 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13126 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13126 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13126 BstLean.Part154.csC) (piBar (rhoBar 13126 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13126 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035218271111 * 1.49465E-7 / (0.000243567119 : ℝ) := by gcongr
    _ ≤ 0.002541047405 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13126 BstLean.Part154.csC Θ ≤ 0.002817822516 + 0.000642083434 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13126 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13126 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13126 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035218271111 : ℝ) * ((2 * Θ * 0.000243567496 +
        (6863 / 10000) * 0.000243567496 * 13126 * 0.000974329310) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002817822516 + 0.000642083434 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13126 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13126 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13126 0.011 Θ ∧ gammaRatio 13126 0.011 Θ ≤ 0.000083732207 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13126 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035218271111 : ℝ) * 0.525 / ((1 - 0.011) * 13126) := by gcongr
      _ ≤ (0.000083732207 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13126 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13126 0.011 Θ) :=
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
    badAllowance 13126 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13126 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13126 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13126 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13126 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13126 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13126 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13126 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13126 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13126 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13126 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035218271111 : ℝ) * 13126 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13126 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003166911002 + 0.003183130839 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13126

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13126
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13126 BstLean.Part154.csC) (piBar (rhoBar 13126 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13126 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13126 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13126 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13126 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13126 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13126 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13126 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13126 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13126 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13126 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13126 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13126 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13126 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13126 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051616448555 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13126) ≤ 0.010423763127 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13126 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035218271111)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010423763127 + 2 * 0.737676 / 13126) := by gcongr
    _ ≤ (0.051616448555 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13126 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13126

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13126
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522208037 : ℝ) ≤ plow 13126 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13126) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052344654693)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334049888) : eMP 13126 0.011 xi bn ≤ 0.001149055596 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13126 : ℝ) * (1 - 0.011))) ≤ 0.000568194009 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001334049888 / (13126 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568194009 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568194009 : ℝ) + 3.141593 * 0.052344654693 / (13126 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001149055596 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052344654693)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334049888) : PiBarMP 13126 12 0.011 xi bn ≤ 0.158586949647 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13126 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036524647678 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.936886037841 : ℝ) ≤ √((13126 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.568756648573 : ℝ) ≤ √(13126 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13126) ≤ 0.121607396906 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036524647678 + 0.052344654693 * 1.772454 / (2 * (113.936886037841 : ℝ))) * (1 + 0.001149055596) +
        8 / (13126 * 114.568756648573) + 0.121607396906 := by gcongr
    _ ≤ (0.158586949647 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052344654693)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334049888) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280405990915) :
    parallelOracle 13126 0.011 xi bn cd ≤ 0.159545369508 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13126 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13126 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522208037 : ℝ) ≤ plow 13126 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.568756648573 : ℝ) ≤ √(13126 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280405990915 : ℝ) / (2 * 0.560522208037 * 114.568756648573)) * 0.158586949647 +
        0.280405990915 ^ 2 / (2 * 0.560522208037 * 114.568756648573) := by gcongr
    _ ≤ (0.159545369508 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052344654693) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001334049888)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280405990915) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13126 13126 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522208037 : ℝ) ≤ plow 13126 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.568756648573 : ℝ) ≤ √(13126 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13126 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13126 Θ 1.22 ≤ 0.011574713201 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.568756648573 := by gcongr <;> linarith
      _ ≤ (0.011574713201 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13126 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13126 13126 0.011 ≤ 0.008343347155 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13126 13126 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13126 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13126 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13126 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13126 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159545369508 + 0.011574713201 + (0.008343347155 : ℝ) *
        (1 + 2 * (0.280405990915 + 0.011574713201) / (0.560522208037 * 114.568756648573))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13126]

end BstLean.Part269.N13126

/-! The original eight local profiles supply actual 13126 moment certificates. -/
namespace BstLean.Part269.N13126
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13126 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13126 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13126 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052344654693 ∧
    0 ≤ bN 13126 BstLean.Part154.csC (groupTheta g) ∧ bN 13126 BstLean.Part154.csC (groupTheta g) ≤ 0.001334049888 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13126 13126 0.011
      (momentAllowance 13126 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13126 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13126 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13126 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13126 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13126 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228789542360 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13126 0.011
      (momentAllowance 13126 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13126 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13126
/-! The actual computed-centre upper energy formula at 13126. -/
namespace BstLean.Part269.N13126
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13126

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13126
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13126)
open BstLean.Part268 (cell13126)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084336340658
  | 2 => 0.085260873925
  | 3 => 0.086181005287
  | 4 => 0.087097554755
  | 5 => 0.088011531193
  | 6 => 0.088924162442
  | 7 => 0.089836928675
  | 8 => 0.090751599102
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13126 13126 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13126 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13126

/-! Actual upper energy certificates on all 43 source endpoints at 13126. -/
namespace BstLean.Part269.N13126
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13126)
open BstLean.Part268 (cell13126)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13126 (gMinus 13126) (1 - (cell13126 i).lower) ≤ 1 ∧
    energyUpper 13126 (gMinus 13126) (BstLean.Part211.gPlus 13126)
      (finiteEnergy 13126 13126 0.011) (1 - (cell13126 i).lower) ≤
      (cell13126 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨10,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨11,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨12,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨13,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨14,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨15,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨16,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨17,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨18,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨19,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨20,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨21,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨22,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨23,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨24,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨25,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨26,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨27,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨28,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨29,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨30,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨31,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨32,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨33,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨34,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨35,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨36,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨37,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨38,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨39,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨40,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨41,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨42,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨43,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨44,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨45,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨46,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨47,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨48,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨49,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨50,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨51,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13126) (by norm_num)
        (q := 1 - (cell13126 ⟨52,by decide⟩).lower)
        (by norm_num [cell13126]) (by norm_num [cell13126])
      exact ⟨E.1,E.2.trans (by norm_num [cell13126])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13126

/-! Source-cell containment and simple scalar guards at 13126. -/
namespace BstLean.Part269.N13126
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13126)
open BstLean.Part268 (cell13126)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13126 ⟨10,by decide⟩).lower ∧ (cell13126 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13126 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13126 ⟨11,by decide⟩).lower ∧ (cell13126 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13126 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13126 ⟨12,by decide⟩).lower ∧ (cell13126 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13126 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13126 ⟨13,by decide⟩).lower ∧ (cell13126 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13126 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13126 ⟨14,by decide⟩).lower ∧ (cell13126 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13126 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13126 ⟨15,by decide⟩).lower ∧ (cell13126 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13126 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13126 ⟨16,by decide⟩).lower ∧ (cell13126 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13126 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13126 ⟨17,by decide⟩).lower ∧ (cell13126 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13126 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13126 ⟨18,by decide⟩).lower ∧ (cell13126 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13126 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13126 ⟨19,by decide⟩).lower ∧ (cell13126 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13126 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13126 ⟨20,by decide⟩).lower ∧ (cell13126 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13126 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13126 ⟨21,by decide⟩).lower ∧ (cell13126 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13126 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13126 ⟨22,by decide⟩).lower ∧ (cell13126 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13126 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13126 ⟨23,by decide⟩).lower ∧ (cell13126 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13126 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13126 ⟨24,by decide⟩).lower ∧ (cell13126 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13126 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13126 ⟨25,by decide⟩).lower ∧ (cell13126 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13126 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13126 ⟨26,by decide⟩).lower ∧ (cell13126 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13126 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13126 ⟨27,by decide⟩).lower ∧ (cell13126 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13126 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13126 ⟨28,by decide⟩).lower ∧ (cell13126 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13126 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13126 ⟨29,by decide⟩).lower ∧ (cell13126 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13126 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13126 ⟨30,by decide⟩).lower ∧ (cell13126 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13126 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13126 ⟨31,by decide⟩).lower ∧ (cell13126 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13126 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13126 ⟨32,by decide⟩).lower ∧ (cell13126 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13126 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13126 ⟨33,by decide⟩).lower ∧ (cell13126 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13126 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13126 ⟨34,by decide⟩).lower ∧ (cell13126 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13126 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13126 ⟨35,by decide⟩).lower ∧ (cell13126 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13126 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13126 ⟨36,by decide⟩).lower ∧ (cell13126 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13126 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13126 ⟨37,by decide⟩).lower ∧ (cell13126 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13126 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13126 ⟨38,by decide⟩).lower ∧ (cell13126 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13126 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13126 ⟨39,by decide⟩).lower ∧ (cell13126 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13126 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13126 ⟨40,by decide⟩).lower ∧ (cell13126 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13126 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13126 ⟨41,by decide⟩).lower ∧ (cell13126 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13126 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13126 ⟨42,by decide⟩).lower ∧ (cell13126 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13126 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13126 ⟨43,by decide⟩).lower ∧ (cell13126 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13126 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13126 ⟨44,by decide⟩).lower ∧ (cell13126 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13126 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13126 ⟨45,by decide⟩).lower ∧ (cell13126 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13126 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13126 ⟨46,by decide⟩).lower ∧ (cell13126 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13126 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13126 ⟨47,by decide⟩).lower ∧ (cell13126 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13126 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13126 ⟨48,by decide⟩).lower ∧ (cell13126 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13126 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13126 ⟨49,by decide⟩).lower ∧ (cell13126 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13126 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13126 ⟨50,by decide⟩).lower ∧ (cell13126 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13126 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13126 ⟨51,by decide⟩).lower ∧ (cell13126 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13126 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13126 ⟨52,by decide⟩).lower ∧ (cell13126 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13126 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13126 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13126 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13126,cell13126,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13126 i).lower ∧
    (cell13126 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13126 i).upper ≤ (0.532 : ℝ) ∧
    (cell13126 i).centre ≤ (0.1 : ℝ) ∧ (cell13126 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13126 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13126 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13126

/-! The local source numeric instances at 13126 have no network premises. -/
namespace BstLean.Part269.N13126
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13126)
open BstLean.Part268 (cell13126)

noncomputable def sourceNumerics13126 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13126 (cell13126 i)
      scalarRow13126.M scalarRow13126.H scalarRow13126.xi := by
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
    energy_allowance := scalarRow13126.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13126]
    centre_nonneg := (scalarRow13126.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13126])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13126
/-! Actual 13127 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13127
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13127 ≤ (1.035216918034 : ℝ) := by
  have hr : (114.573120757008 : ℝ) ≤ √(13127 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.573120757008 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13127 13127 (11 / 1000) ≤
    (0.008343029353 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13127) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.573120757008 : ℝ) ≤ √(13127 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13127)
  have hdiv : K / √(13127 : ℝ) ≤ K / 114.573120757008 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.573120757008 ≤ (0.008343029353 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13127.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13127 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13127 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13127 := gPlus_lower 13127
end BstLean.Part269.N13127

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13127
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035216918033 : ℝ) ≤ wn 13127 := by
  have hn : √(13127 : ℝ) ≤ 114.573120757009 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13127 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.573120757009 ≤ 2 / √(13127 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243548246 : ℝ) ≤ rhoBar 13127 BstLean.Part154.csC ∧
    rhoBar 13127 BstLean.Part154.csC ≤ 0.000243548623 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035216918033 : ℝ) / (1.295212 * 13127) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035216918034 : ℝ) / (1.29521 * 13127) := by gcongr
      _ ≤ (0.000243548623 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13127 BstLean.Part154.csC) ≤ 0.000974253808 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13127 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13127 BstLean.Part154.csC) (piBar (rhoBar 13127 BstLean.Part154.csC)) ≤ 0.000186023795 ∧
    cc1 (rhoBar 13127 BstLean.Part154.csC) (piBar (rhoBar 13127 BstLean.Part154.csC)) ≤ 0.000118368235 ∧
    cc2 (rhoBar 13127 BstLean.Part154.csC) ≤ 0.000068713739 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13127 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13127 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13127 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13127 BstLean.Part154.csC * nuR (rhoBar 13127 BstLean.Part154.csC)) ≤ 0.000487112075 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243548623 : ℝ) * 0.000974253808 := by gcongr
      _ ≤ (0.000487112075 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13127 BstLean.Part154.csC) * nuR (rhoBar 13127 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000974253808 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13127 BstLean.Part154.csC) * rhoBar 13127 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243548623 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243548623 / 2 + 0.399 * 0.000974253808 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186023795 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487112075 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118368235 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243548623 / 1.414213562 := by gcongr
      _ ≤ (0.000068713739 : ℝ) := by norm_num

end BstLean.Part269.N13127

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13127
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13127 BstLean.Part154.csC) (piBar (rhoBar 13127 BstLean.Part154.csC)) ≤ 1.49442E-7 := by
  have hr0 : 0 ≤ rhoBar 13127 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13127 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13127 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13127 BstLean.Part154.csC) (piBar (rhoBar 13127 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13127 BstLean.Part154.csC) (piBar (rhoBar 13127 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13127 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186023795 : ℝ) ^ 2 + 0.000118368235 ^ 2 + 3 * 0.000068713739 ^ 2 +
        2 * 0.797885 * 0.000186023795 * 0.000118368235 + 2 * 0.000186023795 * 0.000068713739 +
        4 * 0.797885 * 0.000118368235 * 0.000068713739 := by gcongr
    _ ≤ (1.49442E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13127 BstLean.Part154.csC Θ ≤ 0.002540849942 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13127 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13127 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13127 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13127 BstLean.Part154.csC) (piBar (rhoBar 13127 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13127 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035216918034 * 1.49442E-7 / (0.000243548246 : ℝ) := by gcongr
    _ ≤ 0.002540849942 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13127 BstLean.Part154.csC Θ ≤ 0.002817596794 + 0.000642032842 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13127 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13127 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13127 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035216918034 : ℝ) * ((2 * Θ * 0.000243548623 +
        (6863 / 10000) * 0.000243548623 * 13127 * 0.000974253808) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002817596794 + 0.000642032842 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13127 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13127 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13127 0.011 Θ ∧ gammaRatio 13127 0.011 Θ ≤ 0.000083725719 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13127 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035216918034 : ℝ) * 0.525 / ((1 - 0.011) * 13127) := by gcongr
      _ ≤ (0.000083725719 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13127 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13127 0.011 Θ) :=
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
    badAllowance 13127 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13127 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13127 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13127 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13127 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13127 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13127 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13127 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13127 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13127 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13127 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035216918034 : ℝ) * 13127 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13127 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003166685280 + 0.003182882784 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13127

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13127
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13127 BstLean.Part154.csC) (piBar (rhoBar 13127 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13127 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13127 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13127 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13127 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13127 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13127 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13127 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13127 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13127 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13127 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13127 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13127 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13127 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13127 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051614461507 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13127) ≤ 0.010423366085 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13127 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035216918034)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010423366085 + 2 * 0.737676 / 13127) := by gcongr
    _ ≤ (0.051614461507 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13127 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13127

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13127
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522250369 : ℝ) ≤ plow 13127 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13127) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052344298742)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333946220) : eMP 13127 0.011 xi bn ≤ 0.001148967107 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13127 : ℝ) * (1 - 0.011))) ≤ 0.000568150290 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001333946220 / (13127 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568150290 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568150290 : ℝ) + 3.141593 * 0.052344298742 / (13127 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001148967107 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052344298742)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333946220) : PiBarMP 13127 12 0.011 xi bn ≤ 0.158580874620 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13127 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036523228500 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.941226077307 : ℝ) ≤ √((13127 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.573120757008 : ℝ) ≤ √(13127 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13127) ≤ 0.121602764861 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036523228500 + 0.052344298742 * 1.772454 / (2 * (113.941226077307 : ℝ))) * (1 + 0.001148967107) +
        8 / (13127 * 114.573120757008) + 0.121602764861 := by gcongr
    _ ≤ (0.158580874620 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052344298742)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333946220) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280403225965) :
    parallelOracle 13127 0.011 xi bn cd ≤ 0.159539229154 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13127 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13127 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522250369 : ℝ) ≤ plow 13127 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.573120757008 : ℝ) ≤ √(13127 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280403225965 : ℝ) / (2 * 0.560522250369 * 114.573120757008)) * 0.158580874620 +
        0.280403225965 ^ 2 / (2 * 0.560522250369 * 114.573120757008) := by gcongr
    _ ≤ (0.159539229154 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052344298742) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333946220)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280403225965) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13127 13127 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522250369 : ℝ) ≤ plow 13127 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.573120757008 : ℝ) ≤ √(13127 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13127 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13127 Θ 1.22 ≤ 0.011574272319 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.573120757008 := by gcongr <;> linarith
      _ ≤ (0.011574272319 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13127 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13127 13127 0.011 ≤ 0.008343029353 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13127 13127 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13127 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13127 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13127 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13127 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159539229154 + 0.011574272319 + (0.008343029353 : ℝ) *
        (1 + 2 * (0.280403225965 + 0.011574272319) / (0.560522250369 * 114.573120757008))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13127]

end BstLean.Part269.N13127

/-! The original eight local profiles supply actual 13127 moment certificates. -/
namespace BstLean.Part269.N13127
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13127 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13127 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13127 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052344298742 ∧
    0 ≤ bN 13127 BstLean.Part154.csC (groupTheta g) ∧ bN 13127 BstLean.Part154.csC (groupTheta g) ≤ 0.001333946220 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13127 13127 0.011
      (momentAllowance 13127 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13127 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13127 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13127 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13127 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13127 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228788764458 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13127 0.011
      (momentAllowance 13127 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13127 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13127
/-! The actual computed-centre upper energy formula at 13127. -/
namespace BstLean.Part269.N13127
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13127

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13127
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13127)
open BstLean.Part268 (cell13127)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084333818536
  | 2 => 0.085258320572
  | 3 => 0.086178416247
  | 4 => 0.087094924508
  | 5 => 0.088008852960
  | 6 => 0.088921427957
  | 7 => 0.089834127935
  | 8 => 0.090748720081
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13127 13127 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13127 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13127

/-! Actual upper energy certificates on all 43 source endpoints at 13127. -/
namespace BstLean.Part269.N13127
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13127)
open BstLean.Part268 (cell13127)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13127 (gMinus 13127) (1 - (cell13127 i).lower) ≤ 1 ∧
    energyUpper 13127 (gMinus 13127) (BstLean.Part211.gPlus 13127)
      (finiteEnergy 13127 13127 0.011) (1 - (cell13127 i).lower) ≤
      (cell13127 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨10,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨11,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨12,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨13,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨14,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨15,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨16,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨17,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨18,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨19,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨20,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨21,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨22,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨23,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨24,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨25,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨26,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨27,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨28,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨29,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨30,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨31,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨32,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨33,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨34,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨35,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨36,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨37,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨38,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨39,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨40,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨41,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨42,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨43,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨44,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨45,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨46,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨47,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨48,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨49,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨50,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨51,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13127) (by norm_num)
        (q := 1 - (cell13127 ⟨52,by decide⟩).lower)
        (by norm_num [cell13127]) (by norm_num [cell13127])
      exact ⟨E.1,E.2.trans (by norm_num [cell13127])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13127

/-! Source-cell containment and simple scalar guards at 13127. -/
namespace BstLean.Part269.N13127
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13127)
open BstLean.Part268 (cell13127)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13127 ⟨10,by decide⟩).lower ∧ (cell13127 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13127 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13127 ⟨11,by decide⟩).lower ∧ (cell13127 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13127 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13127 ⟨12,by decide⟩).lower ∧ (cell13127 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13127 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13127 ⟨13,by decide⟩).lower ∧ (cell13127 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13127 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13127 ⟨14,by decide⟩).lower ∧ (cell13127 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13127 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13127 ⟨15,by decide⟩).lower ∧ (cell13127 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13127 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13127 ⟨16,by decide⟩).lower ∧ (cell13127 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13127 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13127 ⟨17,by decide⟩).lower ∧ (cell13127 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13127 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13127 ⟨18,by decide⟩).lower ∧ (cell13127 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13127 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13127 ⟨19,by decide⟩).lower ∧ (cell13127 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13127 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13127 ⟨20,by decide⟩).lower ∧ (cell13127 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13127 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13127 ⟨21,by decide⟩).lower ∧ (cell13127 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13127 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13127 ⟨22,by decide⟩).lower ∧ (cell13127 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13127 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13127 ⟨23,by decide⟩).lower ∧ (cell13127 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13127 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13127 ⟨24,by decide⟩).lower ∧ (cell13127 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13127 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13127 ⟨25,by decide⟩).lower ∧ (cell13127 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13127 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13127 ⟨26,by decide⟩).lower ∧ (cell13127 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13127 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13127 ⟨27,by decide⟩).lower ∧ (cell13127 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13127 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13127 ⟨28,by decide⟩).lower ∧ (cell13127 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13127 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13127 ⟨29,by decide⟩).lower ∧ (cell13127 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13127 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13127 ⟨30,by decide⟩).lower ∧ (cell13127 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13127 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13127 ⟨31,by decide⟩).lower ∧ (cell13127 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13127 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13127 ⟨32,by decide⟩).lower ∧ (cell13127 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13127 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13127 ⟨33,by decide⟩).lower ∧ (cell13127 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13127 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13127 ⟨34,by decide⟩).lower ∧ (cell13127 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13127 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13127 ⟨35,by decide⟩).lower ∧ (cell13127 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13127 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13127 ⟨36,by decide⟩).lower ∧ (cell13127 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13127 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13127 ⟨37,by decide⟩).lower ∧ (cell13127 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13127 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13127 ⟨38,by decide⟩).lower ∧ (cell13127 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13127 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13127 ⟨39,by decide⟩).lower ∧ (cell13127 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13127 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13127 ⟨40,by decide⟩).lower ∧ (cell13127 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13127 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13127 ⟨41,by decide⟩).lower ∧ (cell13127 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13127 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13127 ⟨42,by decide⟩).lower ∧ (cell13127 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13127 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13127 ⟨43,by decide⟩).lower ∧ (cell13127 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13127 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13127 ⟨44,by decide⟩).lower ∧ (cell13127 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13127 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13127 ⟨45,by decide⟩).lower ∧ (cell13127 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13127 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13127 ⟨46,by decide⟩).lower ∧ (cell13127 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13127 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13127 ⟨47,by decide⟩).lower ∧ (cell13127 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13127 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13127 ⟨48,by decide⟩).lower ∧ (cell13127 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13127 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13127 ⟨49,by decide⟩).lower ∧ (cell13127 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13127 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13127 ⟨50,by decide⟩).lower ∧ (cell13127 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13127 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13127 ⟨51,by decide⟩).lower ∧ (cell13127 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13127 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13127 ⟨52,by decide⟩).lower ∧ (cell13127 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13127 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13127 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13127 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13127,cell13127,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13127 i).lower ∧
    (cell13127 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13127 i).upper ≤ (0.532 : ℝ) ∧
    (cell13127 i).centre ≤ (0.1 : ℝ) ∧ (cell13127 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13127 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13127 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13127

/-! The local source numeric instances at 13127 have no network premises. -/
namespace BstLean.Part269.N13127
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13127)
open BstLean.Part268 (cell13127)

noncomputable def sourceNumerics13127 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13127 (cell13127 i)
      scalarRow13127.M scalarRow13127.H scalarRow13127.xi := by
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
    energy_allowance := scalarRow13127.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13127]
    centre_nonneg := (scalarRow13127.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13127])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13127
/-! Actual 13128 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13128
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13128 ≤ (1.035215565113 : ℝ) := by
  have hr : (114.577484699220 : ℝ) ≤ √(13128 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.577484699220 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13128 13128 (11 / 1000) ≤
    (0.008342711588 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13128) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.577484699220 : ℝ) ≤ √(13128 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13128)
  have hdiv : K / √(13128 : ℝ) ≤ K / 114.577484699220 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.577484699220 ≤ (0.008342711588 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13128.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13128 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13128 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13128 := gPlus_lower 13128
end BstLean.Part269.N13128

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13128
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035215565112 : ℝ) ≤ wn 13128 := by
  have hn : √(13128 : ℝ) ≤ 114.577484699221 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13128 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.577484699221 ≤ 2 / √(13128 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243529376 : ℝ) ≤ rhoBar 13128 BstLean.Part154.csC ∧
    rhoBar 13128 BstLean.Part154.csC ≤ 0.000243529753 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035215565112 : ℝ) / (1.295212 * 13128) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035215565113 : ℝ) / (1.29521 * 13128) := by gcongr
      _ ≤ (0.000243529753 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13128 BstLean.Part154.csC) ≤ 0.000974178319 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13128 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13128 BstLean.Part154.csC) (piBar (rhoBar 13128 BstLean.Part154.csC)) ≤ 0.000186009381 ∧
    cc1 (rhoBar 13128 BstLean.Part154.csC) (piBar (rhoBar 13128 BstLean.Part154.csC)) ≤ 0.000118359063 ∧
    cc2 (rhoBar 13128 BstLean.Part154.csC) ≤ 0.000068708415 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13128 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13128 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13128 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13128 BstLean.Part154.csC * nuR (rhoBar 13128 BstLean.Part154.csC)) ≤ 0.000487074333 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243529753 : ℝ) * 0.000974178319 := by gcongr
      _ ≤ (0.000487074333 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13128 BstLean.Part154.csC) * nuR (rhoBar 13128 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000974178319 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13128 BstLean.Part154.csC) * rhoBar 13128 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243529753 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243529753 / 2 + 0.399 * 0.000974178319 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000186009381 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487074333 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118359063 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243529753 / 1.414213562 := by gcongr
      _ ≤ (0.000068708415 : ℝ) := by norm_num

end BstLean.Part269.N13128

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13128
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13128 BstLean.Part154.csC) (piBar (rhoBar 13128 BstLean.Part154.csC)) ≤ 1.49419E-7 := by
  have hr0 : 0 ≤ rhoBar 13128 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13128 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13128 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13128 BstLean.Part154.csC) (piBar (rhoBar 13128 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13128 BstLean.Part154.csC) (piBar (rhoBar 13128 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13128 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000186009381 : ℝ) ^ 2 + 0.000118359063 ^ 2 + 3 * 0.000068708415 ^ 2 +
        2 * 0.797885 * 0.000186009381 * 0.000118359063 + 2 * 0.000186009381 * 0.000068708415 +
        4 * 0.797885 * 0.000118359063 * 0.000068708415 := by gcongr
    _ ≤ (1.49419E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13128 BstLean.Part154.csC Θ ≤ 0.002540652419 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13128 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13128 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13128 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13128 BstLean.Part154.csC) (piBar (rhoBar 13128 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13128 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035215565113 * 1.49419E-7 / (0.000243529376 : ℝ) := by gcongr
    _ ≤ 0.002540652419 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13128 BstLean.Part154.csC Θ ≤ 0.002817371113 + 0.000641982259 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13128 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13128 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13128 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035215565113 : ℝ) * ((2 * Θ * 0.000243529753 +
        (6863 / 10000) * 0.000243529753 * 13128 * 0.000974178319) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002817371113 + 0.000641982259 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13128 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13128 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13128 0.011 Θ ∧ gammaRatio 13128 0.011 Θ ≤ 0.000083719232 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13128 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035215565113 : ℝ) * 0.525 / ((1 - 0.011) * 13128) := by gcongr
      _ ≤ (0.000083719232 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13128 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13128 0.011 Θ) :=
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
    badAllowance 13128 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13128 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13128 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13128 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13128 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13128 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13128 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13128 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13128 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13128 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13128 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035215565113 : ℝ) * 13128 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13128 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003166459599 + 0.003182634678 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13128

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13128
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13128 BstLean.Part154.csC) (piBar (rhoBar 13128 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13128 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13128 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13128 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13128 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13128 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13128 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13128 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13128 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13128 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13128 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13128 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13128 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13128 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13128 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051612474681 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13128) ≤ 0.010422969087 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13128 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035215565113)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010422969087 + 2 * 0.737676 / 13128) := by gcongr
    _ ≤ (0.051612474681 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13128 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13128

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13128
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522292695 : ℝ) ≤ plow 13128 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13128) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052343942805)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333842520) : eMP 13128 0.011 xi bn ≤ 0.001148878610 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13128 : ℝ) * (1 - 0.011))) ≤ 0.000568106567 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001333842520 / (13128 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568106567 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568106567 : ℝ) + 3.141593 * 0.052343942805 / (13128 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001148878610 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052343942805)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333842520) : PiBarMP 13128 12 0.011 xi bn ≤ 0.158574799629 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13128 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036521808828 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.945565951466 : ℝ) ≤ √((13128 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.577484699220 : ℝ) ≤ √(13128 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13128) ≤ 0.121598133345 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036521808828 + 0.052343942805 * 1.772454 / (2 * (113.945565951466 : ℝ))) * (1 + 0.001148878610) +
        8 / (13128 * 114.577484699220) + 0.121598133345 := by gcongr
    _ ≤ (0.158574799629 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052343942805)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333842520) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280400461265) :
    parallelOracle 13128 0.011 xi bn cd ≤ 0.159533088843 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13128 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13128 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522292695 : ℝ) ≤ plow 13128 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.577484699220 : ℝ) ≤ √(13128 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280400461265 : ℝ) / (2 * 0.560522292695 * 114.577484699220)) * 0.158574799629 +
        0.280400461265 ^ 2 / (2 * 0.560522292695 * 114.577484699220) := by gcongr
    _ ≤ (0.159533088843 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052343942805) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333842520)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280400461265) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13128 13128 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522292695 : ℝ) ≤ plow 13128 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.577484699220 : ℝ) ≤ √(13128 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13128 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13128 Θ 1.22 ≤ 0.011573831487 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.577484699220 := by gcongr <;> linarith
      _ ≤ (0.011573831487 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13128 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13128 13128 0.011 ≤ 0.008342711588 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13128 13128 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13128 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13128 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13128 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13128 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159533088843 + 0.011573831487 + (0.008342711588 : ℝ) *
        (1 + 2 * (0.280400461265 + 0.011573831487) / (0.560522292695 * 114.577484699220))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13128]

end BstLean.Part269.N13128

/-! The original eight local profiles supply actual 13128 moment certificates. -/
namespace BstLean.Part269.N13128
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13128 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13128 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13128 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052343942805 ∧
    0 ≤ bN 13128 BstLean.Part154.csC (groupTheta g) ∧ bN 13128 BstLean.Part154.csC (groupTheta g) ≤ 0.001333842520 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13128 13128 0.011
      (momentAllowance 13128 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13128 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13128 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13128 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13128 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13128 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228787986584 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13128 0.011
      (momentAllowance 13128 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13128 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13128
/-! The actual computed-centre upper energy formula at 13128. -/
namespace BstLean.Part269.N13128
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13128

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13128
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13128)
open BstLean.Part268 (cell13128)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084331297134
  | 2 => 0.085255767963
  | 3 => 0.086175827981
  | 4 => 0.087092295073
  | 5 => 0.088006175584
  | 6 => 0.088918694384
  | 7 => 0.089831328175
  | 8 => 0.090745842123
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13128 13128 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13128 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13128

/-! Actual upper energy certificates on all 43 source endpoints at 13128. -/
namespace BstLean.Part269.N13128
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13128)
open BstLean.Part268 (cell13128)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13128 (gMinus 13128) (1 - (cell13128 i).lower) ≤ 1 ∧
    energyUpper 13128 (gMinus 13128) (BstLean.Part211.gPlus 13128)
      (finiteEnergy 13128 13128 0.011) (1 - (cell13128 i).lower) ≤
      (cell13128 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨10,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨11,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨12,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨13,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨14,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨15,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨16,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨17,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨18,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨19,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨20,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨21,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨22,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨23,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨24,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨25,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨26,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨27,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨28,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨29,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨30,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨31,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨32,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨33,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨34,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨35,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨36,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨37,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨38,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨39,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨40,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨41,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨42,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨43,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨44,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨45,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨46,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨47,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨48,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨49,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨50,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨51,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13128) (by norm_num)
        (q := 1 - (cell13128 ⟨52,by decide⟩).lower)
        (by norm_num [cell13128]) (by norm_num [cell13128])
      exact ⟨E.1,E.2.trans (by norm_num [cell13128])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13128

/-! Source-cell containment and simple scalar guards at 13128. -/
namespace BstLean.Part269.N13128
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13128)
open BstLean.Part268 (cell13128)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13128 ⟨10,by decide⟩).lower ∧ (cell13128 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13128 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13128 ⟨11,by decide⟩).lower ∧ (cell13128 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13128 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13128 ⟨12,by decide⟩).lower ∧ (cell13128 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13128 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13128 ⟨13,by decide⟩).lower ∧ (cell13128 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13128 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13128 ⟨14,by decide⟩).lower ∧ (cell13128 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13128 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13128 ⟨15,by decide⟩).lower ∧ (cell13128 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13128 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13128 ⟨16,by decide⟩).lower ∧ (cell13128 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13128 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13128 ⟨17,by decide⟩).lower ∧ (cell13128 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13128 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13128 ⟨18,by decide⟩).lower ∧ (cell13128 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13128 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13128 ⟨19,by decide⟩).lower ∧ (cell13128 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13128 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13128 ⟨20,by decide⟩).lower ∧ (cell13128 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13128 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13128 ⟨21,by decide⟩).lower ∧ (cell13128 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13128 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13128 ⟨22,by decide⟩).lower ∧ (cell13128 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13128 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13128 ⟨23,by decide⟩).lower ∧ (cell13128 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13128 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13128 ⟨24,by decide⟩).lower ∧ (cell13128 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13128 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13128 ⟨25,by decide⟩).lower ∧ (cell13128 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13128 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13128 ⟨26,by decide⟩).lower ∧ (cell13128 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13128 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13128 ⟨27,by decide⟩).lower ∧ (cell13128 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13128 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13128 ⟨28,by decide⟩).lower ∧ (cell13128 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13128 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13128 ⟨29,by decide⟩).lower ∧ (cell13128 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13128 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13128 ⟨30,by decide⟩).lower ∧ (cell13128 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13128 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13128 ⟨31,by decide⟩).lower ∧ (cell13128 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13128 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13128 ⟨32,by decide⟩).lower ∧ (cell13128 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13128 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13128 ⟨33,by decide⟩).lower ∧ (cell13128 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13128 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13128 ⟨34,by decide⟩).lower ∧ (cell13128 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13128 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13128 ⟨35,by decide⟩).lower ∧ (cell13128 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13128 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13128 ⟨36,by decide⟩).lower ∧ (cell13128 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13128 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13128 ⟨37,by decide⟩).lower ∧ (cell13128 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13128 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13128 ⟨38,by decide⟩).lower ∧ (cell13128 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13128 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13128 ⟨39,by decide⟩).lower ∧ (cell13128 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13128 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13128 ⟨40,by decide⟩).lower ∧ (cell13128 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13128 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13128 ⟨41,by decide⟩).lower ∧ (cell13128 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13128 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13128 ⟨42,by decide⟩).lower ∧ (cell13128 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13128 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13128 ⟨43,by decide⟩).lower ∧ (cell13128 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13128 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13128 ⟨44,by decide⟩).lower ∧ (cell13128 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13128 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13128 ⟨45,by decide⟩).lower ∧ (cell13128 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13128 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13128 ⟨46,by decide⟩).lower ∧ (cell13128 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13128 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13128 ⟨47,by decide⟩).lower ∧ (cell13128 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13128 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13128 ⟨48,by decide⟩).lower ∧ (cell13128 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13128 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13128 ⟨49,by decide⟩).lower ∧ (cell13128 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13128 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13128 ⟨50,by decide⟩).lower ∧ (cell13128 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13128 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13128 ⟨51,by decide⟩).lower ∧ (cell13128 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13128 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13128 ⟨52,by decide⟩).lower ∧ (cell13128 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13128 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13128 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13128 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13128,cell13128,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13128 i).lower ∧
    (cell13128 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13128 i).upper ≤ (0.532 : ℝ) ∧
    (cell13128 i).centre ≤ (0.1 : ℝ) ∧ (cell13128 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13128 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13128 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13128

/-! The local source numeric instances at 13128 have no network premises. -/
namespace BstLean.Part269.N13128
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13128)
open BstLean.Part268 (cell13128)

noncomputable def sourceNumerics13128 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13128 (cell13128 i)
      scalarRow13128.M scalarRow13128.H scalarRow13128.xi := by
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
    energy_allowance := scalarRow13128.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13128]
    centre_nonneg := (scalarRow13128.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13128])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13128
/-! Actual 13129 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13129
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13129 ≤ (1.035214212347 : ℝ) := by
  have hr : (114.581848475227 : ℝ) ≤ √(13129 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.581848475227 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13129 13129 (11 / 1000) ≤
    (0.008342393859 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13129) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.581848475227 : ℝ) ≤ √(13129 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13129)
  have hdiv : K / √(13129 : ℝ) ≤ K / 114.581848475227 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.581848475227 ≤ (0.008342393859 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13129.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13129 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13129 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13129 := gPlus_lower 13129
end BstLean.Part269.N13129

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13129
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035214212346 : ℝ) ≤ wn 13129 := by
  have hn : √(13129 : ℝ) ≤ 114.581848475228 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13129 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.581848475228 ≤ 2 / √(13129 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243510509 : ℝ) ≤ rhoBar 13129 BstLean.Part154.csC ∧
    rhoBar 13129 BstLean.Part154.csC ≤ 0.000243510886 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035214212346 : ℝ) / (1.295212 * 13129) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035214212347 : ℝ) / (1.29521 * 13129) := by gcongr
      _ ≤ (0.000243510886 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13129 BstLean.Part154.csC) ≤ 0.000974102842 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13129 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13129 BstLean.Part154.csC) (piBar (rhoBar 13129 BstLean.Part154.csC)) ≤ 0.000185994970 ∧
    cc1 (rhoBar 13129 BstLean.Part154.csC) (piBar (rhoBar 13129 BstLean.Part154.csC)) ≤ 0.000118349894 ∧
    cc2 (rhoBar 13129 BstLean.Part154.csC) ≤ 0.000068703092 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13129 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13129 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13129 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13129 BstLean.Part154.csC * nuR (rhoBar 13129 BstLean.Part154.csC)) ≤ 0.000487036597 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243510886 : ℝ) * 0.000974102842 := by gcongr
      _ ≤ (0.000487036597 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13129 BstLean.Part154.csC) * nuR (rhoBar 13129 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000974102842 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13129 BstLean.Part154.csC) * rhoBar 13129 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243510886 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243510886 / 2 + 0.399 * 0.000974102842 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185994970 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000487036597 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118349894 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243510886 / 1.414213562 := by gcongr
      _ ≤ (0.000068703092 : ℝ) := by norm_num

end BstLean.Part269.N13129

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13129
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13129 BstLean.Part154.csC) (piBar (rhoBar 13129 BstLean.Part154.csC)) ≤ 1.49396E-7 := by
  have hr0 : 0 ≤ rhoBar 13129 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13129 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13129 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13129 BstLean.Part154.csC) (piBar (rhoBar 13129 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13129 BstLean.Part154.csC) (piBar (rhoBar 13129 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13129 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185994970 : ℝ) ^ 2 + 0.000118349894 ^ 2 + 3 * 0.000068703092 ^ 2 +
        2 * 0.797885 * 0.000185994970 * 0.000118349894 + 2 * 0.000185994970 * 0.000068703092 +
        4 * 0.797885 * 0.000118349894 * 0.000068703092 := by gcongr
    _ ≤ (1.49396E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13129 BstLean.Part154.csC Θ ≤ 0.002540454835 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13129 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13129 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13129 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13129 BstLean.Part154.csC) (piBar (rhoBar 13129 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13129 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035214212347 * 1.49396E-7 / (0.000243510509 : ℝ) := by gcongr
    _ ≤ 0.002540454835 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13129 BstLean.Part154.csC Θ ≤ 0.002817145469 + 0.000641931684 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13129 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13129 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13129 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035214212347 : ℝ) * ((2 * Θ * 0.000243510886 +
        (6863 / 10000) * 0.000243510886 * 13129 * 0.000974102842) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002817145469 + 0.000641931684 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13129 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13129 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13129 0.011 Θ ∧ gammaRatio 13129 0.011 Θ ≤ 0.000083712746 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13129 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035214212347 : ℝ) * 0.525 / ((1 - 0.011) * 13129) := by gcongr
      _ ≤ (0.000083712746 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13129 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13129 0.011 Θ) :=
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
    badAllowance 13129 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13129 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13129 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13129 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13129 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13129 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13129 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13129 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13129 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13129 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13129 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035214212347 : ℝ) * 13129 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13129 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003166233955 + 0.003182386519 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13129

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13129
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13129 BstLean.Part154.csC) (piBar (rhoBar 13129 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13129 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13129 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13129 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13129 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13129 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13129 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13129 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13129 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13129 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13129 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13129 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13129 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13129 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13129 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051610488086 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13129) ≤ 0.010422572135 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13129 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035214212347)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010422572135 + 2 * 0.737676 / 13129) := by gcongr
    _ ≤ (0.051610488086 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13129 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13129

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13129
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522335014 : ℝ) ≤ plow 13129 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13129) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052343586878)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333738789) : eMP 13129 0.011 xi bn ≤ 0.001148790107 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13129 : ℝ) * (1 - 0.011))) ≤ 0.000568062841 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001333738789 / (13129 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568062841 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568062841 : ℝ) + 3.141593 * 0.052343586878 / (13129 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001148790107 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052343586878)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333738789) : PiBarMP 13129 12 0.011 xi bn ≤ 0.158568724689 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13129 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036520388676 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.949905660338 : ℝ) ≤ √((13129 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.581848475227 : ℝ) ≤ √(13129 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13129) ≤ 0.121593502358 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036520388676 + 0.052343586878 * 1.772454 / (2 * (113.949905660338 : ℝ))) * (1 + 0.001148790107) +
        8 / (13129 * 114.581848475227) + 0.121593502358 := by gcongr
    _ ≤ (0.158568724689 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052343586878)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333738789) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280397696815) :
    parallelOracle 13129 0.011 xi bn cd ≤ 0.159526948592 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13129 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13129 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522335014 : ℝ) ≤ plow 13129 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.581848475227 : ℝ) ≤ √(13129 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280397696815 : ℝ) / (2 * 0.560522335014 * 114.581848475227)) * 0.158568724689 +
        0.280397696815 ^ 2 / (2 * 0.560522335014 * 114.581848475227) := by gcongr
    _ ≤ (0.159526948592 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052343586878) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333738789)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280397696815) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13129 13129 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522335014 : ℝ) ≤ plow 13129 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.581848475227 : ℝ) ≤ √(13129 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13129 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13129 Θ 1.22 ≤ 0.011573390705 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.581848475227 := by gcongr <;> linarith
      _ ≤ (0.011573390705 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13129 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13129 13129 0.011 ≤ 0.008342393859 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13129 13129 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13129 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13129 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13129 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13129 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159526948592 + 0.011573390705 + (0.008342393859 : ℝ) *
        (1 + 2 * (0.280397696815 + 0.011573390705) / (0.560522335014 * 114.581848475227))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13129]

end BstLean.Part269.N13129

/-! The original eight local profiles supply actual 13129 moment certificates. -/
namespace BstLean.Part269.N13129
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13129 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13129 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13129 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052343586878 ∧
    0 ≤ bN 13129 BstLean.Part154.csC (groupTheta g) ∧ bN 13129 BstLean.Part154.csC (groupTheta g) ≤ 0.001333738789 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13129 13129 0.011
      (momentAllowance 13129 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13129 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13129 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13129 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13129 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13129 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228787208729 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13129 0.011
      (momentAllowance 13129 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13129 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13129
/-! The actual computed-centre upper energy formula at 13129. -/
namespace BstLean.Part269.N13129
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13129

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13129
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13129)
open BstLean.Part268 (cell13129)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084328776451
  | 2 => 0.085253216098
  | 3 => 0.086173240489
  | 4 => 0.087089666449
  | 5 => 0.088003499064
  | 6 => 0.088915961725
  | 7 => 0.089828529395
  | 8 => 0.090742965227
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13129 13129 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13129 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13129

/-! Actual upper energy certificates on all 43 source endpoints at 13129. -/
namespace BstLean.Part269.N13129
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13129)
open BstLean.Part268 (cell13129)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13129 (gMinus 13129) (1 - (cell13129 i).lower) ≤ 1 ∧
    energyUpper 13129 (gMinus 13129) (BstLean.Part211.gPlus 13129)
      (finiteEnergy 13129 13129 0.011) (1 - (cell13129 i).lower) ≤
      (cell13129 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨10,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨11,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨12,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨13,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨14,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨15,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨16,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨17,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨18,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨19,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨20,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨21,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨22,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨23,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨24,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨25,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨26,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨27,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨28,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨29,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨30,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨31,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨32,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨33,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨34,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨35,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨36,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨37,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨38,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨39,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨40,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨41,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨42,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨43,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨44,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨45,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨46,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨47,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨48,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨49,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨50,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨51,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13129) (by norm_num)
        (q := 1 - (cell13129 ⟨52,by decide⟩).lower)
        (by norm_num [cell13129]) (by norm_num [cell13129])
      exact ⟨E.1,E.2.trans (by norm_num [cell13129])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13129

/-! Source-cell containment and simple scalar guards at 13129. -/
namespace BstLean.Part269.N13129
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13129)
open BstLean.Part268 (cell13129)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13129 ⟨10,by decide⟩).lower ∧ (cell13129 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13129 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13129 ⟨11,by decide⟩).lower ∧ (cell13129 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13129 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13129 ⟨12,by decide⟩).lower ∧ (cell13129 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13129 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13129 ⟨13,by decide⟩).lower ∧ (cell13129 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13129 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13129 ⟨14,by decide⟩).lower ∧ (cell13129 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13129 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13129 ⟨15,by decide⟩).lower ∧ (cell13129 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13129 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13129 ⟨16,by decide⟩).lower ∧ (cell13129 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13129 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13129 ⟨17,by decide⟩).lower ∧ (cell13129 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13129 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13129 ⟨18,by decide⟩).lower ∧ (cell13129 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13129 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13129 ⟨19,by decide⟩).lower ∧ (cell13129 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13129 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13129 ⟨20,by decide⟩).lower ∧ (cell13129 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13129 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13129 ⟨21,by decide⟩).lower ∧ (cell13129 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13129 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13129 ⟨22,by decide⟩).lower ∧ (cell13129 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13129 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13129 ⟨23,by decide⟩).lower ∧ (cell13129 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13129 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13129 ⟨24,by decide⟩).lower ∧ (cell13129 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13129 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13129 ⟨25,by decide⟩).lower ∧ (cell13129 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13129 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13129 ⟨26,by decide⟩).lower ∧ (cell13129 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13129 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13129 ⟨27,by decide⟩).lower ∧ (cell13129 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13129 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13129 ⟨28,by decide⟩).lower ∧ (cell13129 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13129 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13129 ⟨29,by decide⟩).lower ∧ (cell13129 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13129 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13129 ⟨30,by decide⟩).lower ∧ (cell13129 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13129 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13129 ⟨31,by decide⟩).lower ∧ (cell13129 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13129 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13129 ⟨32,by decide⟩).lower ∧ (cell13129 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13129 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13129 ⟨33,by decide⟩).lower ∧ (cell13129 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13129 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13129 ⟨34,by decide⟩).lower ∧ (cell13129 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13129 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13129 ⟨35,by decide⟩).lower ∧ (cell13129 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13129 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13129 ⟨36,by decide⟩).lower ∧ (cell13129 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13129 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13129 ⟨37,by decide⟩).lower ∧ (cell13129 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13129 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13129 ⟨38,by decide⟩).lower ∧ (cell13129 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13129 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13129 ⟨39,by decide⟩).lower ∧ (cell13129 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13129 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13129 ⟨40,by decide⟩).lower ∧ (cell13129 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13129 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13129 ⟨41,by decide⟩).lower ∧ (cell13129 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13129 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13129 ⟨42,by decide⟩).lower ∧ (cell13129 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13129 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13129 ⟨43,by decide⟩).lower ∧ (cell13129 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13129 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13129 ⟨44,by decide⟩).lower ∧ (cell13129 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13129 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13129 ⟨45,by decide⟩).lower ∧ (cell13129 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13129 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13129 ⟨46,by decide⟩).lower ∧ (cell13129 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13129 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13129 ⟨47,by decide⟩).lower ∧ (cell13129 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13129 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13129 ⟨48,by decide⟩).lower ∧ (cell13129 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13129 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13129 ⟨49,by decide⟩).lower ∧ (cell13129 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13129 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13129 ⟨50,by decide⟩).lower ∧ (cell13129 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13129 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13129 ⟨51,by decide⟩).lower ∧ (cell13129 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13129 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13129 ⟨52,by decide⟩).lower ∧ (cell13129 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13129 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13129 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13129 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13129,cell13129,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13129 i).lower ∧
    (cell13129 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13129 i).upper ≤ (0.532 : ℝ) ∧
    (cell13129 i).centre ≤ (0.1 : ℝ) ∧ (cell13129 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13129 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13129 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13129

/-! The local source numeric instances at 13129 have no network premises. -/
namespace BstLean.Part269.N13129
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13129)
open BstLean.Part268 (cell13129)

noncomputable def sourceNumerics13129 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13129 (cell13129 i)
      scalarRow13129.M scalarRow13129.H scalarRow13129.xi := by
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
    energy_allowance := scalarRow13129.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13129]
    centre_nonneg := (scalarRow13129.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13129])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13129
/-! Actual 13130 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13130
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13130 ≤ (1.035212859737 : ℝ) := by
  have hr : (114.586212085049 : ℝ) ≤ √(13130 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.586212085049 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13130 13130 (11 / 1000) ≤
    (0.008342076166 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13130) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.586212085049 : ℝ) ≤ √(13130 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13130)
  have hdiv : K / √(13130 : ℝ) ≤ K / 114.586212085049 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.586212085049 ≤ (0.008342076166 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13130.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13130 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13130 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13130 := gPlus_lower 13130
end BstLean.Part269.N13130

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13130
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035212859736 : ℝ) ≤ wn 13130 := by
  have hn : √(13130 : ℝ) ≤ 114.586212085050 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13130 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.586212085050 ≤ 2 / √(13130 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243491645 : ℝ) ≤ rhoBar 13130 BstLean.Part154.csC ∧
    rhoBar 13130 BstLean.Part154.csC ≤ 0.000243492022 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035212859736 : ℝ) / (1.295212 * 13130) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035212859737 : ℝ) / (1.29521 * 13130) := by gcongr
      _ ≤ (0.000243492022 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13130 BstLean.Part154.csC) ≤ 0.000974027377 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13130 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13130 BstLean.Part154.csC) (piBar (rhoBar 13130 BstLean.Part154.csC)) ≤ 0.000185980561 ∧
    cc1 (rhoBar 13130 BstLean.Part154.csC) (piBar (rhoBar 13130 BstLean.Part154.csC)) ≤ 0.000118340725 ∧
    cc2 (rhoBar 13130 BstLean.Part154.csC) ≤ 0.000068697770 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13130 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13130 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13130 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13130 BstLean.Part154.csC * nuR (rhoBar 13130 BstLean.Part154.csC)) ≤ 0.000486998867 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243492022 : ℝ) * 0.000974027377 := by gcongr
      _ ≤ (0.000486998867 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13130 BstLean.Part154.csC) * nuR (rhoBar 13130 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000974027377 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13130 BstLean.Part154.csC) * rhoBar 13130 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243492022 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243492022 / 2 + 0.399 * 0.000974027377 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185980561 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486998867 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118340725 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243492022 / 1.414213562 := by gcongr
      _ ≤ (0.000068697770 : ℝ) := by norm_num

end BstLean.Part269.N13130

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13130
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13130 BstLean.Part154.csC) (piBar (rhoBar 13130 BstLean.Part154.csC)) ≤ 1.49373E-7 := by
  have hr0 : 0 ≤ rhoBar 13130 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13130 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13130 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13130 BstLean.Part154.csC) (piBar (rhoBar 13130 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13130 BstLean.Part154.csC) (piBar (rhoBar 13130 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13130 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185980561 : ℝ) ^ 2 + 0.000118340725 ^ 2 + 3 * 0.000068697770 ^ 2 +
        2 * 0.797885 * 0.000185980561 * 0.000118340725 + 2 * 0.000185980561 * 0.000068697770 +
        4 * 0.797885 * 0.000118340725 * 0.000068697770 := by gcongr
    _ ≤ (1.49373E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13130 BstLean.Part154.csC Θ ≤ 0.002540257191 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13130 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13130 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13130 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13130 BstLean.Part154.csC) (piBar (rhoBar 13130 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13130 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035212859737 * 1.49373E-7 / (0.000243491645 : ℝ) := by gcongr
    _ ≤ 0.002540257191 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13130 BstLean.Part154.csC Θ ≤ 0.002816919864 + 0.000641881117 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13130 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13130 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13130 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035212859737 : ℝ) * ((2 * Θ * 0.000243492022 +
        (6863 / 10000) * 0.000243492022 * 13130 * 0.000974027377) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002816919864 + 0.000641881117 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13130 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13130 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13130 0.011 Θ ∧ gammaRatio 13130 0.011 Θ ≤ 0.000083706261 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13130 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035212859737 : ℝ) * 0.525 / ((1 - 0.011) * 13130) := by gcongr
      _ ≤ (0.000083706261 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13130 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13130 0.011 Θ) :=
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
    badAllowance 13130 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13130 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13130 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13130 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13130 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13130 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13130 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13130 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13130 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13130 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13130 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035212859737 : ℝ) * 13130 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13130 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003166008350 + 0.003182138308 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13130

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13130
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13130 BstLean.Part154.csC) (piBar (rhoBar 13130 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13130 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13130 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13130 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13130 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13130 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13130 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13130 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13130 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13130 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13130 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13130 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13130 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13130 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13130 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051608501719 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13130) ≤ 0.010422175228 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13130 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035212859737)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010422175228 + 2 * 0.737676 / 13130) := by gcongr
    _ ≤ (0.051608501719 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13130 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13130

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13130
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522377326 : ℝ) ≤ plow 13130 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13130) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052343230962)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333635026) : eMP 13130 0.011 xi bn ≤ 0.001148701598 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13130 : ℝ) * (1 - 0.011))) ≤ 0.000568019112 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001333635026 / (13130 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000568019112 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000568019112 : ℝ) + 3.141593 * 0.052343230962 / (13130 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001148701598 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052343230962)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333635026) : PiBarMP 13130 12 0.011 xi bn ≤ 0.158562649787 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13130 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036518968031 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.954245203941 : ℝ) ≤ √((13130 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.586212085049 : ℝ) ≤ √(13130 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13130) ≤ 0.121588871901 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036518968031 + 0.052343230962 * 1.772454 / (2 * (113.954245203941 : ℝ))) * (1 + 0.001148701598) +
        8 / (13130 * 114.586212085049) + 0.121588871901 := by gcongr
    _ ≤ (0.158562649787 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052343230962)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333635026) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280394932615) :
    parallelOracle 13130 0.011 xi bn cd ≤ 0.159520808387 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13130 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13130 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522377326 : ℝ) ≤ plow 13130 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.586212085049 : ℝ) ≤ √(13130 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280394932615 : ℝ) / (2 * 0.560522377326 * 114.586212085049)) * 0.158562649787 +
        0.280394932615 ^ 2 / (2 * 0.560522377326 * 114.586212085049) := by gcongr
    _ ≤ (0.159520808387 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052343230962) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333635026)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280394932615) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13130 13130 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522377326 : ℝ) ≤ plow 13130 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.586212085049 : ℝ) ≤ √(13130 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13130 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13130 Θ 1.22 ≤ 0.011572949973 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.586212085049 := by gcongr <;> linarith
      _ ≤ (0.011572949973 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13130 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13130 13130 0.011 ≤ 0.008342076166 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13130 13130 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13130 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13130 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13130 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13130 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159520808387 + 0.011572949973 + (0.008342076166 : ℝ) *
        (1 + 2 * (0.280394932615 + 0.011572949973) / (0.560522377326 * 114.586212085049))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13130]

end BstLean.Part269.N13130

/-! The original eight local profiles supply actual 13130 moment certificates. -/
namespace BstLean.Part269.N13130
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13130 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13130 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13130 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052343230962 ∧
    0 ≤ bN 13130 BstLean.Part154.csC (groupTheta g) ∧ bN 13130 BstLean.Part154.csC (groupTheta g) ≤ 0.001333635026 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13130 13130 0.011
      (momentAllowance 13130 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13130 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13130 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13130 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13130 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13130 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228786430896 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13130 0.011
      (momentAllowance 13130 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13130 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13130
/-! The actual computed-centre upper energy formula at 13130. -/
namespace BstLean.Part269.N13130
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13130

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13130
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13130)
open BstLean.Part268 (cell13130)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084326256487
  | 2 => 0.085250664975
  | 3 => 0.086170653769
  | 4 => 0.087087038634
  | 5 => 0.088000823400
  | 6 => 0.088913229976
  | 7 => 0.089825731595
  | 8 => 0.090740089392
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13130 13130 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13130 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13130

/-! Actual upper energy certificates on all 43 source endpoints at 13130. -/
namespace BstLean.Part269.N13130
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13130)
open BstLean.Part268 (cell13130)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13130 (gMinus 13130) (1 - (cell13130 i).lower) ≤ 1 ∧
    energyUpper 13130 (gMinus 13130) (BstLean.Part211.gPlus 13130)
      (finiteEnergy 13130 13130 0.011) (1 - (cell13130 i).lower) ≤
      (cell13130 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨10,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨11,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨12,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨13,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨14,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨15,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨16,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨17,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨18,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨19,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨20,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨21,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨22,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨23,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨24,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨25,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨26,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨27,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨28,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨29,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨30,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨31,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨32,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨33,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨34,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨35,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨36,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨37,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨38,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨39,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨40,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨41,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨42,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨43,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨44,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨45,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨46,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨47,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨48,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨49,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨50,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨51,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13130) (by norm_num)
        (q := 1 - (cell13130 ⟨52,by decide⟩).lower)
        (by norm_num [cell13130]) (by norm_num [cell13130])
      exact ⟨E.1,E.2.trans (by norm_num [cell13130])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13130

/-! Source-cell containment and simple scalar guards at 13130. -/
namespace BstLean.Part269.N13130
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13130)
open BstLean.Part268 (cell13130)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13130 ⟨10,by decide⟩).lower ∧ (cell13130 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13130 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13130 ⟨11,by decide⟩).lower ∧ (cell13130 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13130 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13130 ⟨12,by decide⟩).lower ∧ (cell13130 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13130 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13130 ⟨13,by decide⟩).lower ∧ (cell13130 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13130 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13130 ⟨14,by decide⟩).lower ∧ (cell13130 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13130 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13130 ⟨15,by decide⟩).lower ∧ (cell13130 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13130 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13130 ⟨16,by decide⟩).lower ∧ (cell13130 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13130 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13130 ⟨17,by decide⟩).lower ∧ (cell13130 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13130 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13130 ⟨18,by decide⟩).lower ∧ (cell13130 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13130 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13130 ⟨19,by decide⟩).lower ∧ (cell13130 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13130 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13130 ⟨20,by decide⟩).lower ∧ (cell13130 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13130 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13130 ⟨21,by decide⟩).lower ∧ (cell13130 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13130 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13130 ⟨22,by decide⟩).lower ∧ (cell13130 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13130 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13130 ⟨23,by decide⟩).lower ∧ (cell13130 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13130 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13130 ⟨24,by decide⟩).lower ∧ (cell13130 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13130 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13130 ⟨25,by decide⟩).lower ∧ (cell13130 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13130 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13130 ⟨26,by decide⟩).lower ∧ (cell13130 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13130 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13130 ⟨27,by decide⟩).lower ∧ (cell13130 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13130 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13130 ⟨28,by decide⟩).lower ∧ (cell13130 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13130 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13130 ⟨29,by decide⟩).lower ∧ (cell13130 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13130 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13130 ⟨30,by decide⟩).lower ∧ (cell13130 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13130 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13130 ⟨31,by decide⟩).lower ∧ (cell13130 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13130 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13130 ⟨32,by decide⟩).lower ∧ (cell13130 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13130 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13130 ⟨33,by decide⟩).lower ∧ (cell13130 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13130 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13130 ⟨34,by decide⟩).lower ∧ (cell13130 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13130 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13130 ⟨35,by decide⟩).lower ∧ (cell13130 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13130 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13130 ⟨36,by decide⟩).lower ∧ (cell13130 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13130 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13130 ⟨37,by decide⟩).lower ∧ (cell13130 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13130 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13130 ⟨38,by decide⟩).lower ∧ (cell13130 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13130 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13130 ⟨39,by decide⟩).lower ∧ (cell13130 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13130 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13130 ⟨40,by decide⟩).lower ∧ (cell13130 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13130 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13130 ⟨41,by decide⟩).lower ∧ (cell13130 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13130 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13130 ⟨42,by decide⟩).lower ∧ (cell13130 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13130 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13130 ⟨43,by decide⟩).lower ∧ (cell13130 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13130 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13130 ⟨44,by decide⟩).lower ∧ (cell13130 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13130 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13130 ⟨45,by decide⟩).lower ∧ (cell13130 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13130 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13130 ⟨46,by decide⟩).lower ∧ (cell13130 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13130 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13130 ⟨47,by decide⟩).lower ∧ (cell13130 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13130 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13130 ⟨48,by decide⟩).lower ∧ (cell13130 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13130 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13130 ⟨49,by decide⟩).lower ∧ (cell13130 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13130 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13130 ⟨50,by decide⟩).lower ∧ (cell13130 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13130 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13130 ⟨51,by decide⟩).lower ∧ (cell13130 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13130 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13130 ⟨52,by decide⟩).lower ∧ (cell13130 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13130 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13130 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13130 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13130,cell13130,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13130 i).lower ∧
    (cell13130 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13130 i).upper ≤ (0.532 : ℝ) ∧
    (cell13130 i).centre ≤ (0.1 : ℝ) ∧ (cell13130 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13130 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13130 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13130

/-! The local source numeric instances at 13130 have no network premises. -/
namespace BstLean.Part269.N13130
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13130)
open BstLean.Part268 (cell13130)

noncomputable def sourceNumerics13130 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13130 (cell13130 i)
      scalarRow13130.M scalarRow13130.H scalarRow13130.xi := by
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
    energy_allowance := scalarRow13130.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13130]
    centre_nonneg := (scalarRow13130.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13130])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13130
/-! Actual 13131 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13131
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13131 ≤ (1.035211507282 : ℝ) := by
  have hr : (114.590575528705 : ℝ) ≤ √(13131 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.590575528705 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13131 13131 (11 / 1000) ≤
    (0.008341758509 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13131) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.590575528705 : ℝ) ≤ √(13131 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13131)
  have hdiv : K / √(13131 : ℝ) ≤ K / 114.590575528705 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.590575528705 ≤ (0.008341758509 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13131.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13131 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13131 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13131 := gPlus_lower 13131
end BstLean.Part269.N13131

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13131
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035211507281 : ℝ) ≤ wn 13131 := by
  have hn : √(13131 : ℝ) ≤ 114.590575528706 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13131 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.590575528706 ≤ 2 / √(13131 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243472783 : ℝ) ≤ rhoBar 13131 BstLean.Part154.csC ∧
    rhoBar 13131 BstLean.Part154.csC ≤ 0.000243473160 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035211507281 : ℝ) / (1.295212 * 13131) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035211507282 : ℝ) / (1.29521 * 13131) := by gcongr
      _ ≤ (0.000243473160 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13131 BstLean.Part154.csC) ≤ 0.000973951920 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13131 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13131 BstLean.Part154.csC) (piBar (rhoBar 13131 BstLean.Part154.csC)) ≤ 0.000185966153 ∧
    cc1 (rhoBar 13131 BstLean.Part154.csC) (piBar (rhoBar 13131 BstLean.Part154.csC)) ≤ 0.000118331558 ∧
    cc2 (rhoBar 13131 BstLean.Part154.csC) ≤ 0.000068692448 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13131 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13131 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13131 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13131 BstLean.Part154.csC * nuR (rhoBar 13131 BstLean.Part154.csC)) ≤ 0.000486961140 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243473160 : ℝ) * 0.000973951920 := by gcongr
      _ ≤ (0.000486961140 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13131 BstLean.Part154.csC) * nuR (rhoBar 13131 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000973951920 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13131 BstLean.Part154.csC) * rhoBar 13131 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243473160 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243473160 / 2 + 0.399 * 0.000973951920 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185966153 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486961140 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118331558 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243473160 / 1.414213562 := by gcongr
      _ ≤ (0.000068692448 : ℝ) := by norm_num

end BstLean.Part269.N13131

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13131
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13131 BstLean.Part154.csC) (piBar (rhoBar 13131 BstLean.Part154.csC)) ≤ 1.49350E-7 := by
  have hr0 : 0 ≤ rhoBar 13131 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13131 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13131 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13131 BstLean.Part154.csC) (piBar (rhoBar 13131 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13131 BstLean.Part154.csC) (piBar (rhoBar 13131 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13131 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185966153 : ℝ) ^ 2 + 0.000118331558 ^ 2 + 3 * 0.000068692448 ^ 2 +
        2 * 0.797885 * 0.000185966153 * 0.000118331558 + 2 * 0.000185966153 * 0.000068692448 +
        4 * 0.797885 * 0.000118331558 * 0.000068692448 := by gcongr
    _ ≤ (1.49350E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13131 BstLean.Part154.csC Θ ≤ 0.002540059496 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13131 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13131 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13131 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13131 BstLean.Part154.csC) (piBar (rhoBar 13131 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13131 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035211507282 * 1.49350E-7 / (0.000243472783 : ℝ) := by gcongr
    _ ≤ 0.002540059496 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13131 BstLean.Part154.csC Θ ≤ 0.002816694273 + 0.000641830555 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13131 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13131 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13131 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035211507282 : ℝ) * ((2 * Θ * 0.000243473160 +
        (6863 / 10000) * 0.000243473160 * 13131 * 0.000973951920) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002816694273 + 0.000641830555 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13131 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13131 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13131 0.011 Θ ∧ gammaRatio 13131 0.011 Θ ≤ 0.000083699777 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13131 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035211507282 : ℝ) * 0.525 / ((1 - 0.011) * 13131) := by gcongr
      _ ≤ (0.000083699777 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13131 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13131 0.011 Θ) :=
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
    badAllowance 13131 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13131 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13131 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13131 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13131 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13131 0.011 Θ) 1.12 ≤ 1.5230E-8 := by
    have he : (18.0 : ℝ) ≤ gap 1 (gammaRatio 13131 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13131 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13131 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_0_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13131 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13131 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035211507282 : ℝ) * 13131 *
        (1.2470E-8 / 1.1045361 + 1.5230E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13131 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003165782759 + 0.003181890051 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13131

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13131
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13131 BstLean.Part154.csC) (piBar (rhoBar 13131 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13131 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13131 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13131 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13131 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13131 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13131 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13131 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13131 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13131 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13131 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13131 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13131 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13131 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13131 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051606515583 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13131) ≤ 0.010421778367 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13131 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035211507282)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010421778367 + 2 * 0.737676 / 13131) := by gcongr
    _ ≤ (0.051606515583 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13131 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13131

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13131
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522419632 : ℝ) ≤ plow 13131 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13131) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052342875036)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333531236) : eMP 13131 0.011 xi bn ≤ 0.001148613084 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13131 : ℝ) * (1 - 0.011))) ≤ 0.000567975380 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001333531236 / (13131 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567975380 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567975380 : ℝ) + 3.141593 * 0.052342875036 / (13131 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001148613084 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052342875036)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333531236) : PiBarMP 13131 12 0.011 xi bn ≤ 0.158556574990 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13131 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036517546961 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.958584582294 : ℝ) ≤ √((13131 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.590575528705 : ℝ) ≤ √(13131 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13131) ≤ 0.121584241972 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036517546961 + 0.052342875036 * 1.772454 / (2 * (113.958584582294 : ℝ))) * (1 + 0.001148613084) +
        8 / (13131 * 114.590575528705) + 0.121584241972 := by gcongr
    _ ≤ (0.158556574990 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052342875036)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333531236) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280392168621) :
    parallelOracle 13131 0.011 xi bn cd ≤ 0.159514668296 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13131 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13131 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522419632 : ℝ) ≤ plow 13131 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.590575528705 : ℝ) ≤ √(13131 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280392168621 : ℝ) / (2 * 0.560522419632 * 114.590575528705)) * 0.158556574990 +
        0.280392168621 ^ 2 / (2 * 0.560522419632 * 114.590575528705) := by gcongr
    _ ≤ (0.159514668296 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052342875036) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333531236)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280392168621) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13131 13131 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522419632 : ℝ) ≤ plow 13131 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.590575528705 : ℝ) ≤ √(13131 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13131 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13131 Θ 1.22 ≤ 0.011572509292 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.590575528705 := by gcongr <;> linarith
      _ ≤ (0.011572509292 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13131 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13131 13131 0.011 ≤ 0.008341758509 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13131 13131 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13131 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13131 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13131 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13131 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159514668296 + 0.011572509292 + (0.008341758509 : ℝ) *
        (1 + 2 * (0.280392168621 + 0.011572509292) / (0.560522419632 * 114.590575528705))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13131]

end BstLean.Part269.N13131

/-! The original eight local profiles supply actual 13131 moment certificates. -/
namespace BstLean.Part269.N13131
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13131 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13131 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13131 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052342875036 ∧
    0 ≤ bN 13131 BstLean.Part154.csC (groupTheta g) ∧ bN 13131 BstLean.Part154.csC (groupTheta g) ≤ 0.001333531236 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13131 13131 0.011
      (momentAllowance 13131 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13131 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13131 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13131 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13131 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13131 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228785653038 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13131 0.011
      (momentAllowance 13131 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13131 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13131
/-! The actual computed-centre upper energy formula at 13131. -/
namespace BstLean.Part269.N13131
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13131

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13131
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13131)
open BstLean.Part268 (cell13131)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084323737241
  | 2 => 0.085248114595
  | 3 => 0.086168067822
  | 4 => 0.087084411629
  | 5 => 0.087998148591
  | 6 => 0.088910499138
  | 7 => 0.089822934772
  | 8 => 0.090737214618
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13131 13131 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13131 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13131

/-! Actual upper energy certificates on all 43 source endpoints at 13131. -/
namespace BstLean.Part269.N13131
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13131)
open BstLean.Part268 (cell13131)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13131 (gMinus 13131) (1 - (cell13131 i).lower) ≤ 1 ∧
    energyUpper 13131 (gMinus 13131) (BstLean.Part211.gPlus 13131)
      (finiteEnergy 13131 13131 0.011) (1 - (cell13131 i).lower) ≤
      (cell13131 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨10,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨11,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨12,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨13,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨14,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨15,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨16,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨17,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨18,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨19,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨20,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨21,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨22,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨23,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨24,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨25,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨26,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨27,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨28,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨29,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨30,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨31,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨32,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨33,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨34,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨35,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨36,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨37,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨38,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨39,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨40,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨41,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨42,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨43,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨44,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨45,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨46,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨47,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨48,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨49,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨50,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨51,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13131) (by norm_num)
        (q := 1 - (cell13131 ⟨52,by decide⟩).lower)
        (by norm_num [cell13131]) (by norm_num [cell13131])
      exact ⟨E.1,E.2.trans (by norm_num [cell13131])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13131

/-! Source-cell containment and simple scalar guards at 13131. -/
namespace BstLean.Part269.N13131
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13131)
open BstLean.Part268 (cell13131)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13131 ⟨10,by decide⟩).lower ∧ (cell13131 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13131 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13131 ⟨11,by decide⟩).lower ∧ (cell13131 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13131 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13131 ⟨12,by decide⟩).lower ∧ (cell13131 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13131 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13131 ⟨13,by decide⟩).lower ∧ (cell13131 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13131 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13131 ⟨14,by decide⟩).lower ∧ (cell13131 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13131 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13131 ⟨15,by decide⟩).lower ∧ (cell13131 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13131 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13131 ⟨16,by decide⟩).lower ∧ (cell13131 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13131 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13131 ⟨17,by decide⟩).lower ∧ (cell13131 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13131 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13131 ⟨18,by decide⟩).lower ∧ (cell13131 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13131 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13131 ⟨19,by decide⟩).lower ∧ (cell13131 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13131 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13131 ⟨20,by decide⟩).lower ∧ (cell13131 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13131 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13131 ⟨21,by decide⟩).lower ∧ (cell13131 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13131 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13131 ⟨22,by decide⟩).lower ∧ (cell13131 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13131 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13131 ⟨23,by decide⟩).lower ∧ (cell13131 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13131 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13131 ⟨24,by decide⟩).lower ∧ (cell13131 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13131 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13131 ⟨25,by decide⟩).lower ∧ (cell13131 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13131 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13131 ⟨26,by decide⟩).lower ∧ (cell13131 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13131 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13131 ⟨27,by decide⟩).lower ∧ (cell13131 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13131 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13131 ⟨28,by decide⟩).lower ∧ (cell13131 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13131 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13131 ⟨29,by decide⟩).lower ∧ (cell13131 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13131 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13131 ⟨30,by decide⟩).lower ∧ (cell13131 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13131 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13131 ⟨31,by decide⟩).lower ∧ (cell13131 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13131 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13131 ⟨32,by decide⟩).lower ∧ (cell13131 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13131 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13131 ⟨33,by decide⟩).lower ∧ (cell13131 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13131 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13131 ⟨34,by decide⟩).lower ∧ (cell13131 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13131 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13131 ⟨35,by decide⟩).lower ∧ (cell13131 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13131 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13131 ⟨36,by decide⟩).lower ∧ (cell13131 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13131 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13131 ⟨37,by decide⟩).lower ∧ (cell13131 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13131 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13131 ⟨38,by decide⟩).lower ∧ (cell13131 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13131 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13131 ⟨39,by decide⟩).lower ∧ (cell13131 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13131 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13131 ⟨40,by decide⟩).lower ∧ (cell13131 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13131 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13131 ⟨41,by decide⟩).lower ∧ (cell13131 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13131 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13131 ⟨42,by decide⟩).lower ∧ (cell13131 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13131 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13131 ⟨43,by decide⟩).lower ∧ (cell13131 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13131 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13131 ⟨44,by decide⟩).lower ∧ (cell13131 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13131 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13131 ⟨45,by decide⟩).lower ∧ (cell13131 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13131 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13131 ⟨46,by decide⟩).lower ∧ (cell13131 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13131 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13131 ⟨47,by decide⟩).lower ∧ (cell13131 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13131 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13131 ⟨48,by decide⟩).lower ∧ (cell13131 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13131 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13131 ⟨49,by decide⟩).lower ∧ (cell13131 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13131 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13131 ⟨50,by decide⟩).lower ∧ (cell13131 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13131 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13131 ⟨51,by decide⟩).lower ∧ (cell13131 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13131 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13131 ⟨52,by decide⟩).lower ∧ (cell13131 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13131 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13131 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13131 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13131,cell13131,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13131 i).lower ∧
    (cell13131 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13131 i).upper ≤ (0.532 : ℝ) ∧
    (cell13131 i).centre ≤ (0.1 : ℝ) ∧ (cell13131 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13131 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13131 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13131

/-! The local source numeric instances at 13131 have no network premises. -/
namespace BstLean.Part269.N13131
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13131)
open BstLean.Part268 (cell13131)

noncomputable def sourceNumerics13131 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13131 (cell13131 i)
      scalarRow13131.M scalarRow13131.H scalarRow13131.xi := by
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
    energy_allowance := scalarRow13131.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13131]
    centre_nonneg := (scalarRow13131.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13131])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13131
/-! Actual 13132 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13132
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13132 ≤ (1.035210154983 : ℝ) := by
  have hr : (114.594938806214 : ℝ) ≤ √(13132 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.594938806214 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13132 13132 (11 / 1000) ≤
    (0.008341440889 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13132) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.594938806214 : ℝ) ≤ √(13132 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13132)
  have hdiv : K / √(13132 : ℝ) ≤ K / 114.594938806214 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.594938806214 ≤ (0.008341440889 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13132.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13132 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13132 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13132 := gPlus_lower 13132
end BstLean.Part269.N13132

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13132
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035210154982 : ℝ) ≤ wn 13132 := by
  have hn : √(13132 : ℝ) ≤ 114.594938806215 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13132 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.594938806215 ≤ 2 / √(13132 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243453925 : ℝ) ≤ rhoBar 13132 BstLean.Part154.csC ∧
    rhoBar 13132 BstLean.Part154.csC ≤ 0.000243454302 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035210154982 : ℝ) / (1.295212 * 13132) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035210154983 : ℝ) / (1.29521 * 13132) := by gcongr
      _ ≤ (0.000243454302 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13132 BstLean.Part154.csC) ≤ 0.000973876478 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13132 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13132 BstLean.Part154.csC) (piBar (rhoBar 13132 BstLean.Part154.csC)) ≤ 0.000185951749 ∧
    cc1 (rhoBar 13132 BstLean.Part154.csC) (piBar (rhoBar 13132 BstLean.Part154.csC)) ≤ 0.000118322392 ∧
    cc2 (rhoBar 13132 BstLean.Part154.csC) ≤ 0.000068687127 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13132 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13132 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13132 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13132 BstLean.Part154.csC * nuR (rhoBar 13132 BstLean.Part154.csC)) ≤ 0.000486923422 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243454302 : ℝ) * 0.000973876478 := by gcongr
      _ ≤ (0.000486923422 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13132 BstLean.Part154.csC) * nuR (rhoBar 13132 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000973876478 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13132 BstLean.Part154.csC) * rhoBar 13132 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243454302 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243454302 / 2 + 0.399 * 0.000973876478 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185951749 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486923422 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118322392 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243454302 / 1.414213562 := by gcongr
      _ ≤ (0.000068687127 : ℝ) := by norm_num

end BstLean.Part269.N13132

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13132
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13132 BstLean.Part154.csC) (piBar (rhoBar 13132 BstLean.Part154.csC)) ≤ 1.49326E-7 := by
  have hr0 : 0 ≤ rhoBar 13132 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13132 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13132 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13132 BstLean.Part154.csC) (piBar (rhoBar 13132 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13132 BstLean.Part154.csC) (piBar (rhoBar 13132 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13132 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185951749 : ℝ) ^ 2 + 0.000118322392 ^ 2 + 3 * 0.000068687127 ^ 2 +
        2 * 0.797885 * 0.000185951749 * 0.000118322392 + 2 * 0.000185951749 * 0.000068687127 +
        4 * 0.797885 * 0.000118322392 * 0.000068687127 := by gcongr
    _ ≤ (1.49326E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13132 BstLean.Part154.csC Θ ≤ 0.002539844722 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13132 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13132 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13132 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13132 BstLean.Part154.csC) (piBar (rhoBar 13132 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13132 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035210154983 * 1.49326E-7 / (0.000243453925 : ℝ) := by gcongr
    _ ≤ 0.002539844722 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13132 BstLean.Part154.csC Θ ≤ 0.002816468740 + 0.000641780004 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13132 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13132 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13132 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035210154983 : ℝ) * ((2 * Θ * 0.000243454302 +
        (6863 / 10000) * 0.000243454302 * 13132 * 0.000973876478) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002816468740 + 0.000641780004 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13132 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13132 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13132 0.011 Θ ∧ gammaRatio 13132 0.011 Θ ≤ 0.000083693294 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13132 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035210154983 : ℝ) * 0.525 / ((1 - 0.011) * 13132) := by gcongr
      _ ≤ (0.000083693294 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13132 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13132 0.011 Θ) :=
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
    badAllowance 13132 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13132 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13132 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13132 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13132 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13132 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13132 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13132 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13132 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13132 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13132 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035210154983 : ℝ) * 13132 *
        (1.2470E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13132 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003165557226 + 0.003181624726 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13132

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13132
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13132 BstLean.Part154.csC) (piBar (rhoBar 13132 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13132 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13132 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13132 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13132 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13132 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13132 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13132 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13132 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13132 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13132 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13132 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13132 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13132 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13132 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051604529674 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13132) ≤ 0.010421381551 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13132 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035210154983)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010421381551 + 2 * 0.737676 / 13132) := by gcongr
    _ ≤ (0.051604529674 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13132 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13132

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13132
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522461932 : ℝ) ≤ plow 13132 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13132) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052342510208)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333418480) : eMP 13132 0.011 xi bn ≤ 0.001148520755 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13132 : ℝ) * (1 - 0.011))) ≤ 0.000567929742 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001333418480 / (13132 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567929742 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567929742 : ℝ) + 3.141593 * 0.052342510208 / (13132 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001148520755 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052342510208)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333418480) : PiBarMP 13132 12 0.011 xi bn ≤ 0.158550377550 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13132 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036516003068 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.962923795416 : ℝ) ≤ √((13132 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.594938806214 : ℝ) ≤ √(13132 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13132) ≤ 0.121579612572 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036516003068 + 0.052342510208 * 1.772454 / (2 * (113.962923795416 : ℝ))) * (1 + 0.001148520755) +
        8 / (13132 * 114.594938806214) + 0.121579612572 := by gcongr
    _ ≤ (0.158550377550 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052342510208)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333418480) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280389385397) :
    parallelOracle 13132 0.011 xi bn cd ≤ 0.159508405192 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13132 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13132 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522461932 : ℝ) ≤ plow 13132 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.594938806214 : ℝ) ≤ √(13132 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280389385397 : ℝ) / (2 * 0.560522461932 * 114.594938806214)) * 0.158550377550 +
        0.280389385397 ^ 2 / (2 * 0.560522461932 * 114.594938806214) := by gcongr
    _ ≤ (0.159508405192 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052342510208) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333418480)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280389385397) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13132 13132 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522461932 : ℝ) ≤ plow 13132 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.594938806214 : ℝ) ≤ √(13132 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13132 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13132 Θ 1.22 ≤ 0.011572068661 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.594938806214 := by gcongr <;> linarith
      _ ≤ (0.011572068661 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13132 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13132 13132 0.011 ≤ 0.008341440889 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13132 13132 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13132 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13132 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13132 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13132 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159508405192 + 0.011572068661 + (0.008341440889 : ℝ) *
        (1 + 2 * (0.280389385397 + 0.011572068661) / (0.560522461932 * 114.594938806214))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13132]

end BstLean.Part269.N13132

/-! The original eight local profiles supply actual 13132 moment certificates. -/
namespace BstLean.Part269.N13132
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13132 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13132 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13132 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052342510208 ∧
    0 ≤ bN 13132 BstLean.Part154.csC (groupTheta g) ∧ bN 13132 BstLean.Part154.csC (groupTheta g) ≤ 0.001333418480 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13132 13132 0.011
      (momentAllowance 13132 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13132 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13132 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13132 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13132 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13132 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228784855723 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13132 0.011
      (momentAllowance 13132 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13132 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13132
/-! The actual computed-centre upper energy formula at 13132. -/
namespace BstLean.Part269.N13132
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13132

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13132
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13132)
open BstLean.Part268 (cell13132)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084321218713
  | 2 => 0.085245564956
  | 3 => 0.086165482646
  | 4 => 0.087081785432
  | 5 => 0.087995474635
  | 6 => 0.088907769209
  | 7 => 0.089820138927
  | 8 => 0.090734340902
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13132 13132 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13132 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13132

/-! Actual upper energy certificates on all 43 source endpoints at 13132. -/
namespace BstLean.Part269.N13132
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13132)
open BstLean.Part268 (cell13132)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13132 (gMinus 13132) (1 - (cell13132 i).lower) ≤ 1 ∧
    energyUpper 13132 (gMinus 13132) (BstLean.Part211.gPlus 13132)
      (finiteEnergy 13132 13132 0.011) (1 - (cell13132 i).lower) ≤
      (cell13132 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨10,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨11,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨12,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨13,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨14,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨15,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨16,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨17,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨18,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨19,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨20,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨21,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨22,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨23,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨24,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨25,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨26,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨27,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨28,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨29,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨30,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨31,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨32,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨33,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨34,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨35,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨36,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨37,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨38,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨39,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨40,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨41,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨42,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨43,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨44,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨45,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨46,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨47,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨48,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨49,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨50,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨51,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13132) (by norm_num)
        (q := 1 - (cell13132 ⟨52,by decide⟩).lower)
        (by norm_num [cell13132]) (by norm_num [cell13132])
      exact ⟨E.1,E.2.trans (by norm_num [cell13132])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13132

/-! Source-cell containment and simple scalar guards at 13132. -/
namespace BstLean.Part269.N13132
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13132)
open BstLean.Part268 (cell13132)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13132 ⟨10,by decide⟩).lower ∧ (cell13132 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13132 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13132 ⟨11,by decide⟩).lower ∧ (cell13132 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13132 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13132 ⟨12,by decide⟩).lower ∧ (cell13132 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13132 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13132 ⟨13,by decide⟩).lower ∧ (cell13132 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13132 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13132 ⟨14,by decide⟩).lower ∧ (cell13132 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13132 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13132 ⟨15,by decide⟩).lower ∧ (cell13132 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13132 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13132 ⟨16,by decide⟩).lower ∧ (cell13132 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13132 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13132 ⟨17,by decide⟩).lower ∧ (cell13132 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13132 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13132 ⟨18,by decide⟩).lower ∧ (cell13132 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13132 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13132 ⟨19,by decide⟩).lower ∧ (cell13132 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13132 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13132 ⟨20,by decide⟩).lower ∧ (cell13132 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13132 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13132 ⟨21,by decide⟩).lower ∧ (cell13132 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13132 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13132 ⟨22,by decide⟩).lower ∧ (cell13132 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13132 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13132 ⟨23,by decide⟩).lower ∧ (cell13132 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13132 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13132 ⟨24,by decide⟩).lower ∧ (cell13132 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13132 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13132 ⟨25,by decide⟩).lower ∧ (cell13132 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13132 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13132 ⟨26,by decide⟩).lower ∧ (cell13132 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13132 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13132 ⟨27,by decide⟩).lower ∧ (cell13132 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13132 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13132 ⟨28,by decide⟩).lower ∧ (cell13132 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13132 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13132 ⟨29,by decide⟩).lower ∧ (cell13132 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13132 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13132 ⟨30,by decide⟩).lower ∧ (cell13132 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13132 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13132 ⟨31,by decide⟩).lower ∧ (cell13132 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13132 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13132 ⟨32,by decide⟩).lower ∧ (cell13132 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13132 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13132 ⟨33,by decide⟩).lower ∧ (cell13132 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13132 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13132 ⟨34,by decide⟩).lower ∧ (cell13132 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13132 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13132 ⟨35,by decide⟩).lower ∧ (cell13132 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13132 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13132 ⟨36,by decide⟩).lower ∧ (cell13132 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13132 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13132 ⟨37,by decide⟩).lower ∧ (cell13132 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13132 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13132 ⟨38,by decide⟩).lower ∧ (cell13132 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13132 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13132 ⟨39,by decide⟩).lower ∧ (cell13132 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13132 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13132 ⟨40,by decide⟩).lower ∧ (cell13132 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13132 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13132 ⟨41,by decide⟩).lower ∧ (cell13132 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13132 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13132 ⟨42,by decide⟩).lower ∧ (cell13132 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13132 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13132 ⟨43,by decide⟩).lower ∧ (cell13132 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13132 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13132 ⟨44,by decide⟩).lower ∧ (cell13132 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13132 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13132 ⟨45,by decide⟩).lower ∧ (cell13132 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13132 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13132 ⟨46,by decide⟩).lower ∧ (cell13132 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13132 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13132 ⟨47,by decide⟩).lower ∧ (cell13132 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13132 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13132 ⟨48,by decide⟩).lower ∧ (cell13132 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13132 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13132 ⟨49,by decide⟩).lower ∧ (cell13132 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13132 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13132 ⟨50,by decide⟩).lower ∧ (cell13132 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13132 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13132 ⟨51,by decide⟩).lower ∧ (cell13132 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13132 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13132 ⟨52,by decide⟩).lower ∧ (cell13132 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13132 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13132 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13132 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13132,cell13132,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13132 i).lower ∧
    (cell13132 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13132 i).upper ≤ (0.532 : ℝ) ∧
    (cell13132 i).centre ≤ (0.1 : ℝ) ∧ (cell13132 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13132 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13132 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13132

/-! The local source numeric instances at 13132 have no network premises. -/
namespace BstLean.Part269.N13132
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13132)
open BstLean.Part268 (cell13132)

noncomputable def sourceNumerics13132 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13132 (cell13132 i)
      scalarRow13132.M scalarRow13132.H scalarRow13132.xi := by
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
    energy_allowance := scalarRow13132.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13132]
    centre_nonneg := (scalarRow13132.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13132])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13132
/-! Actual 13133 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13133
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13133 ≤ (1.035208802838 : ℝ) := by
  have hr : (114.599301917594 : ℝ) ≤ √(13133 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.599301917594 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13133 13133 (11 / 1000) ≤
    (0.008341123305 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13133) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.599301917594 : ℝ) ≤ √(13133 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13133)
  have hdiv : K / √(13133 : ℝ) ≤ K / 114.599301917594 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.599301917594 ≤ (0.008341123305 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13133.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13133 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13133 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13133 := gPlus_lower 13133
end BstLean.Part269.N13133

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13133
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035208802837 : ℝ) ≤ wn 13133 := by
  have hn : √(13133 : ℝ) ≤ 114.599301917595 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13133 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.599301917595 ≤ 2 / √(13133 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243435069 : ℝ) ≤ rhoBar 13133 BstLean.Part154.csC ∧
    rhoBar 13133 BstLean.Part154.csC ≤ 0.000243435446 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035208802837 : ℝ) / (1.295212 * 13133) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035208802838 : ℝ) / (1.29521 * 13133) := by gcongr
      _ ≤ (0.000243435446 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13133 BstLean.Part154.csC) ≤ 0.000973801045 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13133 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13133 BstLean.Part154.csC) (piBar (rhoBar 13133 BstLean.Part154.csC)) ≤ 0.000185937346 ∧
    cc1 (rhoBar 13133 BstLean.Part154.csC) (piBar (rhoBar 13133 BstLean.Part154.csC)) ≤ 0.000118313228 ∧
    cc2 (rhoBar 13133 BstLean.Part154.csC) ≤ 0.000068681808 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13133 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13133 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13133 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13133 BstLean.Part154.csC * nuR (rhoBar 13133 BstLean.Part154.csC)) ≤ 0.000486885708 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243435446 : ℝ) * 0.000973801045 := by gcongr
      _ ≤ (0.000486885708 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13133 BstLean.Part154.csC) * nuR (rhoBar 13133 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000973801045 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13133 BstLean.Part154.csC) * rhoBar 13133 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243435446 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243435446 / 2 + 0.399 * 0.000973801045 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185937346 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486885708 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118313228 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243435446 / 1.414213562 := by gcongr
      _ ≤ (0.000068681808 : ℝ) := by norm_num

end BstLean.Part269.N13133

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13133
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13133 BstLean.Part154.csC) (piBar (rhoBar 13133 BstLean.Part154.csC)) ≤ 1.49303E-7 := by
  have hr0 : 0 ≤ rhoBar 13133 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13133 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13133 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13133 BstLean.Part154.csC) (piBar (rhoBar 13133 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13133 BstLean.Part154.csC) (piBar (rhoBar 13133 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13133 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185937346 : ℝ) ^ 2 + 0.000118313228 ^ 2 + 3 * 0.000068681808 ^ 2 +
        2 * 0.797885 * 0.000185937346 * 0.000118313228 + 2 * 0.000185937346 * 0.000068681808 +
        4 * 0.797885 * 0.000118313228 * 0.000068681808 := by gcongr
    _ ≤ (1.49303E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13133 BstLean.Part154.csC Θ ≤ 0.002539646906 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13133 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13133 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13133 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13133 BstLean.Part154.csC) (piBar (rhoBar 13133 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13133 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035208802838 * 1.49303E-7 / (0.000243435069 : ℝ) := by gcongr
    _ ≤ 0.002539646906 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13133 BstLean.Part154.csC Θ ≤ 0.002816243224 + 0.000641729459 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13133 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13133 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13133 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035208802838 : ℝ) * ((2 * Θ * 0.000243435446 +
        (6863 / 10000) * 0.000243435446 * 13133 * 0.000973801045) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002816243224 + 0.000641729459 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13133 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13133 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13133 0.011 Θ ∧ gammaRatio 13133 0.011 Θ ≤ 0.000083686812 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13133 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035208802838 : ℝ) * 0.525 / ((1 - 0.011) * 13133) := by gcongr
      _ ≤ (0.000083686812 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13133 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13133 0.011 Θ) :=
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
    badAllowance 13133 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13133 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13133 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13133 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13133 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13133 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13133 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13133 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13133 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13133 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13133 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035208802838 : ℝ) * 13133 *
        (1.2470E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13133 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003165331710 + 0.003181376365 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13133

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13133
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13133 BstLean.Part154.csC) (piBar (rhoBar 13133 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13133 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13133 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13133 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13133 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13133 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13133 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13133 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13133 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13133 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13133 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13133 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13133 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13133 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13133 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051602543992 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13133) ≤ 0.010420984780 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13133 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035208802838)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010420984780 + 2 * 0.737676 / 13133) := by gcongr
    _ ≤ (0.051602543992 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13133 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13133

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13133
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522504225 : ℝ) ≤ plow 13133 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13133) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052342154302)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333314626) : eMP 13133 0.011 xi bn ≤ 0.001148432227 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13133 : ℝ) * (1 - 0.011))) ≤ 0.000567886003 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001333314626 / (13133 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567886003 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567886003 : ℝ) + 3.141593 * 0.052342154302 / (13133 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001148432227 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052342154302)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333314626) : PiBarMP 13133 12 0.011 xi bn ≤ 0.158544302823 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13133 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036514581006 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.967262843327 : ℝ) ≤ √((13133 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.599301917594 : ℝ) ≤ √(13133 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13133) ≤ 0.121574983701 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036514581006 + 0.052342154302 * 1.772454 / (2 * (113.967262843327 : ℝ))) * (1 + 0.001148432227) +
        8 / (13133 * 114.599301917594) + 0.121574983701 := by gcongr
    _ ≤ (0.158544302823 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052342154302)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333314626) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280386621896) :
    parallelOracle 13133 0.011 xi bn cd ≤ 0.159502265187 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13133 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13133 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522504225 : ℝ) ≤ plow 13133 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.599301917594 : ℝ) ≤ √(13133 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280386621896 : ℝ) / (2 * 0.560522504225 * 114.599301917594)) * 0.158544302823 +
        0.280386621896 ^ 2 / (2 * 0.560522504225 * 114.599301917594) := by gcongr
    _ ≤ (0.159502265187 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052342154302) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333314626)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280386621896) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13133 13133 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522504225 : ℝ) ≤ plow 13133 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.599301917594 : ℝ) ≤ √(13133 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13133 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13133 Θ 1.22 ≤ 0.011571628080 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.599301917594 := by gcongr <;> linarith
      _ ≤ (0.011571628080 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13133 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13133 13133 0.011 ≤ 0.008341123305 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13133 13133 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13133 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13133 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13133 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13133 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159502265187 + 0.011571628080 + (0.008341123305 : ℝ) *
        (1 + 2 * (0.280386621896 + 0.011571628080) / (0.560522504225 * 114.599301917594))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13133]

end BstLean.Part269.N13133

/-! The original eight local profiles supply actual 13133 moment certificates. -/
namespace BstLean.Part269.N13133
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13133 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13133 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13133 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052342154302 ∧
    0 ≤ bN 13133 BstLean.Part154.csC (groupTheta g) ∧ bN 13133 BstLean.Part154.csC (groupTheta g) ≤ 0.001333314626 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13133 13133 0.011
      (momentAllowance 13133 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13133 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13133 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13133 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13133 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13133 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228784077904 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13133 0.011
      (momentAllowance 13133 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13133 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13133
/-! The actual computed-centre upper energy formula at 13133. -/
namespace BstLean.Part269.N13133
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13133

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13133
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13133)
open BstLean.Part268 (cell13133)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084318700901
  | 2 => 0.085243016058
  | 3 => 0.086162898241
  | 4 => 0.087079160043
  | 5 => 0.087992801533
  | 6 => 0.088905040189
  | 7 => 0.089817344058
  | 8 => 0.090731468244
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13133 13133 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13133 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13133

/-! Actual upper energy certificates on all 43 source endpoints at 13133. -/
namespace BstLean.Part269.N13133
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13133)
open BstLean.Part268 (cell13133)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13133 (gMinus 13133) (1 - (cell13133 i).lower) ≤ 1 ∧
    energyUpper 13133 (gMinus 13133) (BstLean.Part211.gPlus 13133)
      (finiteEnergy 13133 13133 0.011) (1 - (cell13133 i).lower) ≤
      (cell13133 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨10,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨11,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨12,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨13,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨14,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨15,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨16,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨17,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨18,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨19,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨20,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨21,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨22,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨23,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨24,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨25,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨26,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨27,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨28,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨29,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨30,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨31,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨32,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨33,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨34,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨35,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨36,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨37,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨38,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨39,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨40,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨41,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨42,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨43,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨44,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨45,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨46,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨47,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨48,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨49,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨50,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨51,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13133) (by norm_num)
        (q := 1 - (cell13133 ⟨52,by decide⟩).lower)
        (by norm_num [cell13133]) (by norm_num [cell13133])
      exact ⟨E.1,E.2.trans (by norm_num [cell13133])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13133

/-! Source-cell containment and simple scalar guards at 13133. -/
namespace BstLean.Part269.N13133
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13133)
open BstLean.Part268 (cell13133)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13133 ⟨10,by decide⟩).lower ∧ (cell13133 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13133 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13133 ⟨11,by decide⟩).lower ∧ (cell13133 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13133 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13133 ⟨12,by decide⟩).lower ∧ (cell13133 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13133 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13133 ⟨13,by decide⟩).lower ∧ (cell13133 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13133 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13133 ⟨14,by decide⟩).lower ∧ (cell13133 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13133 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13133 ⟨15,by decide⟩).lower ∧ (cell13133 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13133 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13133 ⟨16,by decide⟩).lower ∧ (cell13133 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13133 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13133 ⟨17,by decide⟩).lower ∧ (cell13133 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13133 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13133 ⟨18,by decide⟩).lower ∧ (cell13133 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13133 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13133 ⟨19,by decide⟩).lower ∧ (cell13133 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13133 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13133 ⟨20,by decide⟩).lower ∧ (cell13133 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13133 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13133 ⟨21,by decide⟩).lower ∧ (cell13133 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13133 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13133 ⟨22,by decide⟩).lower ∧ (cell13133 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13133 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13133 ⟨23,by decide⟩).lower ∧ (cell13133 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13133 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13133 ⟨24,by decide⟩).lower ∧ (cell13133 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13133 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13133 ⟨25,by decide⟩).lower ∧ (cell13133 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13133 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13133 ⟨26,by decide⟩).lower ∧ (cell13133 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13133 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13133 ⟨27,by decide⟩).lower ∧ (cell13133 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13133 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13133 ⟨28,by decide⟩).lower ∧ (cell13133 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13133 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13133 ⟨29,by decide⟩).lower ∧ (cell13133 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13133 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13133 ⟨30,by decide⟩).lower ∧ (cell13133 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13133 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13133 ⟨31,by decide⟩).lower ∧ (cell13133 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13133 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13133 ⟨32,by decide⟩).lower ∧ (cell13133 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13133 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13133 ⟨33,by decide⟩).lower ∧ (cell13133 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13133 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13133 ⟨34,by decide⟩).lower ∧ (cell13133 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13133 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13133 ⟨35,by decide⟩).lower ∧ (cell13133 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13133 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13133 ⟨36,by decide⟩).lower ∧ (cell13133 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13133 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13133 ⟨37,by decide⟩).lower ∧ (cell13133 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13133 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13133 ⟨38,by decide⟩).lower ∧ (cell13133 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13133 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13133 ⟨39,by decide⟩).lower ∧ (cell13133 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13133 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13133 ⟨40,by decide⟩).lower ∧ (cell13133 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13133 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13133 ⟨41,by decide⟩).lower ∧ (cell13133 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13133 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13133 ⟨42,by decide⟩).lower ∧ (cell13133 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13133 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13133 ⟨43,by decide⟩).lower ∧ (cell13133 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13133 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13133 ⟨44,by decide⟩).lower ∧ (cell13133 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13133 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13133 ⟨45,by decide⟩).lower ∧ (cell13133 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13133 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13133 ⟨46,by decide⟩).lower ∧ (cell13133 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13133 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13133 ⟨47,by decide⟩).lower ∧ (cell13133 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13133 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13133 ⟨48,by decide⟩).lower ∧ (cell13133 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13133 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13133 ⟨49,by decide⟩).lower ∧ (cell13133 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13133 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13133 ⟨50,by decide⟩).lower ∧ (cell13133 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13133 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13133 ⟨51,by decide⟩).lower ∧ (cell13133 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13133 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13133 ⟨52,by decide⟩).lower ∧ (cell13133 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13133 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13133 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13133 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13133,cell13133,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13133 i).lower ∧
    (cell13133 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13133 i).upper ≤ (0.532 : ℝ) ∧
    (cell13133 i).centre ≤ (0.1 : ℝ) ∧ (cell13133 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13133 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13133 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13133

/-! The local source numeric instances at 13133 have no network premises. -/
namespace BstLean.Part269.N13133
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13133)
open BstLean.Part268 (cell13133)

noncomputable def sourceNumerics13133 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13133 (cell13133 i)
      scalarRow13133.M scalarRow13133.H scalarRow13133.xi := by
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
    energy_allowance := scalarRow13133.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13133]
    centre_nonneg := (scalarRow13133.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13133])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13133
/-! Actual 13134 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13134
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13134 ≤ (1.035207450850 : ℝ) := by
  have hr : (114.603664862865 : ℝ) ≤ √(13134 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.603664862865 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13134 13134 (11 / 1000) ≤
    (0.008340805757 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13134) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.603664862865 : ℝ) ≤ √(13134 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13134)
  have hdiv : K / √(13134 : ℝ) ≤ K / 114.603664862865 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.603664862865 ≤ (0.008340805757 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13134.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13134 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13134 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13134 := gPlus_lower 13134
end BstLean.Part269.N13134

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13134
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035207450849 : ℝ) ≤ wn 13134 := by
  have hn : √(13134 : ℝ) ≤ 114.603664862866 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13134 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.603664862866 ≤ 2 / √(13134 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243416217 : ℝ) ≤ rhoBar 13134 BstLean.Part154.csC ∧
    rhoBar 13134 BstLean.Part154.csC ≤ 0.000243416594 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035207450849 : ℝ) / (1.295212 * 13134) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035207450850 : ℝ) / (1.29521 * 13134) := by gcongr
      _ ≤ (0.000243416594 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13134 BstLean.Part154.csC) ≤ 0.000973725628 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13134 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13134 BstLean.Part154.csC) (piBar (rhoBar 13134 BstLean.Part154.csC)) ≤ 0.000185922946 ∧
    cc1 (rhoBar 13134 BstLean.Part154.csC) (piBar (rhoBar 13134 BstLean.Part154.csC)) ≤ 0.000118304065 ∧
    cc2 (rhoBar 13134 BstLean.Part154.csC) ≤ 0.000068676489 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13134 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13134 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13134 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13134 BstLean.Part154.csC * nuR (rhoBar 13134 BstLean.Part154.csC)) ≤ 0.000486848001 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243416594 : ℝ) * 0.000973725628 := by gcongr
      _ ≤ (0.000486848001 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13134 BstLean.Part154.csC) * nuR (rhoBar 13134 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000973725628 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13134 BstLean.Part154.csC) * rhoBar 13134 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243416594 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243416594 / 2 + 0.399 * 0.000973725628 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185922946 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486848001 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118304065 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243416594 / 1.414213562 := by gcongr
      _ ≤ (0.000068676489 : ℝ) := by norm_num

end BstLean.Part269.N13134

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13134
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13134 BstLean.Part154.csC) (piBar (rhoBar 13134 BstLean.Part154.csC)) ≤ 1.49280E-7 := by
  have hr0 : 0 ≤ rhoBar 13134 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13134 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13134 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13134 BstLean.Part154.csC) (piBar (rhoBar 13134 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13134 BstLean.Part154.csC) (piBar (rhoBar 13134 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13134 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185922946 : ℝ) ^ 2 + 0.000118304065 ^ 2 + 3 * 0.000068676489 ^ 2 +
        2 * 0.797885 * 0.000185922946 * 0.000118304065 + 2 * 0.000185922946 * 0.000068676489 +
        4 * 0.797885 * 0.000118304065 * 0.000068676489 := by gcongr
    _ ≤ (1.49280E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13134 BstLean.Part154.csC Θ ≤ 0.002539449018 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13134 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13134 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13134 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13134 BstLean.Part154.csC) (piBar (rhoBar 13134 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13134 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035207450850 * 1.49280E-7 / (0.000243416217 : ℝ) := by gcongr
    _ ≤ 0.002539449018 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13134 BstLean.Part154.csC Θ ≤ 0.002816017769 + 0.000641678924 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13134 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13134 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13134 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035207450850 : ℝ) * ((2 * Θ * 0.000243416594 +
        (6863 / 10000) * 0.000243416594 * 13134 * 0.000973725628) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002816017769 + 0.000641678924 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13134 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13134 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13134 0.011 Θ ∧ gammaRatio 13134 0.011 Θ ≤ 0.000083680331 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13134 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035207450850 : ℝ) * 0.525 / ((1 - 0.011) * 13134) := by gcongr
      _ ≤ (0.000083680331 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13134 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13134 0.011 Θ) :=
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
    badAllowance 13134 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13134 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13134 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13134 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13134 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13134 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13134 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13134 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13134 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13134 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13134 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035207450850 : ℝ) * 13134 *
        (1.2470E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13134 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003165106255 + 0.003181127942 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13134

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13134
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13134 BstLean.Part154.csC) (piBar (rhoBar 13134 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13134 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13134 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13134 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13134 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13134 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13134 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13134 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13134 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13134 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13134 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13134 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13134 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13134 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13134 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051600558542 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13134) ≤ 0.010420588055 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13134 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035207450850)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010420588055 + 2 * 0.737676 / 13134) := by gcongr
    _ ≤ (0.051600558542 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13134 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13134

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13134
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522546512 : ℝ) ≤ plow 13134 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13134) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052341798425)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333210735) : eMP 13134 0.011 xi bn ≤ 0.001148343689 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13134 : ℝ) * (1 - 0.011))) ≤ 0.000567842259 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001333210735 / (13134 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567842259 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567842259 : ℝ) + 3.141593 * 0.052341798425 / (13134 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001148343689 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052341798425)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333210735) : PiBarMP 13134 12 0.011 xi bn ≤ 0.158538228064 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13134 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036513158382 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.971601726044 : ℝ) ≤ √((13134 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.603664862865 : ℝ) ≤ √(13134 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13134) ≤ 0.121570355359 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036513158382 + 0.052341798425 * 1.772454 / (2 * (113.971601726044 : ℝ))) * (1 + 0.001148343689) +
        8 / (13134 * 114.603664862865) + 0.121570355359 := by gcongr
    _ ≤ (0.158538228064 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052341798425)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333210735) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280383858687) :
    parallelOracle 13134 0.011 xi bn cd ≤ 0.159496125158 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13134 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13134 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522546512 : ℝ) ≤ plow 13134 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.603664862865 : ℝ) ≤ √(13134 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280383858687 : ℝ) / (2 * 0.560522546512 * 114.603664862865)) * 0.158538228064 +
        0.280383858687 ^ 2 / (2 * 0.560522546512 * 114.603664862865) := by gcongr
    _ ≤ (0.159496125158 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052341798425) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333210735)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280383858687) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13134 13134 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522546512 : ℝ) ≤ plow 13134 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.603664862865 : ℝ) ≤ √(13134 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13134 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13134 Θ 1.22 ≤ 0.011571187550 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.603664862865 := by gcongr <;> linarith
      _ ≤ (0.011571187550 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13134 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13134 13134 0.011 ≤ 0.008340805757 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13134 13134 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13134 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13134 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13134 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13134 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159496125158 + 0.011571187550 + (0.008340805757 : ℝ) *
        (1 + 2 * (0.280383858687 + 0.011571187550) / (0.560522546512 * 114.603664862865))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13134]

end BstLean.Part269.N13134

/-! The original eight local profiles supply actual 13134 moment certificates. -/
namespace BstLean.Part269.N13134
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13134 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13134 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13134 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052341798425 ∧
    0 ≤ bN 13134 BstLean.Part154.csC (groupTheta g) ∧ bN 13134 BstLean.Part154.csC (groupTheta g) ≤ 0.001333210735 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13134 13134 0.011
      (momentAllowance 13134 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13134 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13134 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13134 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13134 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13134 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228783300145 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13134 0.011
      (momentAllowance 13134 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13134 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13134
/-! The actual computed-centre upper energy formula at 13134. -/
namespace BstLean.Part269.N13134
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13134

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13134
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13134)
open BstLean.Part268 (cell13134)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084316183806
  | 2 => 0.085240467901
  | 3 => 0.086160314606
  | 4 => 0.087076535461
  | 5 => 0.087990129283
  | 6 => 0.088902312077
  | 7 => 0.089814550164
  | 8 => 0.090728596643
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13134 13134 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13134 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13134

/-! Actual upper energy certificates on all 43 source endpoints at 13134. -/
namespace BstLean.Part269.N13134
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13134)
open BstLean.Part268 (cell13134)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13134 (gMinus 13134) (1 - (cell13134 i).lower) ≤ 1 ∧
    energyUpper 13134 (gMinus 13134) (BstLean.Part211.gPlus 13134)
      (finiteEnergy 13134 13134 0.011) (1 - (cell13134 i).lower) ≤
      (cell13134 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨10,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨11,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨12,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨13,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨14,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨15,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨16,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨17,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨18,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨19,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨20,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨21,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨22,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨23,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨24,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨25,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨26,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨27,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨28,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨29,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨30,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨31,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨32,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨33,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨34,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨35,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨36,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨37,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨38,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨39,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨40,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨41,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨42,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨43,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨44,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨45,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨46,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨47,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨48,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨49,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨50,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨51,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13134) (by norm_num)
        (q := 1 - (cell13134 ⟨52,by decide⟩).lower)
        (by norm_num [cell13134]) (by norm_num [cell13134])
      exact ⟨E.1,E.2.trans (by norm_num [cell13134])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13134

/-! Source-cell containment and simple scalar guards at 13134. -/
namespace BstLean.Part269.N13134
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13134)
open BstLean.Part268 (cell13134)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13134 ⟨10,by decide⟩).lower ∧ (cell13134 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13134 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13134 ⟨11,by decide⟩).lower ∧ (cell13134 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13134 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13134 ⟨12,by decide⟩).lower ∧ (cell13134 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13134 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13134 ⟨13,by decide⟩).lower ∧ (cell13134 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13134 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13134 ⟨14,by decide⟩).lower ∧ (cell13134 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13134 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13134 ⟨15,by decide⟩).lower ∧ (cell13134 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13134 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13134 ⟨16,by decide⟩).lower ∧ (cell13134 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13134 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13134 ⟨17,by decide⟩).lower ∧ (cell13134 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13134 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13134 ⟨18,by decide⟩).lower ∧ (cell13134 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13134 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13134 ⟨19,by decide⟩).lower ∧ (cell13134 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13134 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13134 ⟨20,by decide⟩).lower ∧ (cell13134 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13134 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13134 ⟨21,by decide⟩).lower ∧ (cell13134 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13134 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13134 ⟨22,by decide⟩).lower ∧ (cell13134 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13134 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13134 ⟨23,by decide⟩).lower ∧ (cell13134 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13134 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13134 ⟨24,by decide⟩).lower ∧ (cell13134 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13134 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13134 ⟨25,by decide⟩).lower ∧ (cell13134 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13134 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13134 ⟨26,by decide⟩).lower ∧ (cell13134 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13134 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13134 ⟨27,by decide⟩).lower ∧ (cell13134 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13134 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13134 ⟨28,by decide⟩).lower ∧ (cell13134 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13134 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13134 ⟨29,by decide⟩).lower ∧ (cell13134 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13134 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13134 ⟨30,by decide⟩).lower ∧ (cell13134 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13134 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13134 ⟨31,by decide⟩).lower ∧ (cell13134 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13134 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13134 ⟨32,by decide⟩).lower ∧ (cell13134 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13134 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13134 ⟨33,by decide⟩).lower ∧ (cell13134 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13134 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13134 ⟨34,by decide⟩).lower ∧ (cell13134 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13134 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13134 ⟨35,by decide⟩).lower ∧ (cell13134 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13134 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13134 ⟨36,by decide⟩).lower ∧ (cell13134 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13134 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13134 ⟨37,by decide⟩).lower ∧ (cell13134 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13134 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13134 ⟨38,by decide⟩).lower ∧ (cell13134 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13134 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13134 ⟨39,by decide⟩).lower ∧ (cell13134 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13134 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13134 ⟨40,by decide⟩).lower ∧ (cell13134 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13134 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13134 ⟨41,by decide⟩).lower ∧ (cell13134 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13134 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13134 ⟨42,by decide⟩).lower ∧ (cell13134 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13134 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13134 ⟨43,by decide⟩).lower ∧ (cell13134 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13134 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13134 ⟨44,by decide⟩).lower ∧ (cell13134 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13134 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13134 ⟨45,by decide⟩).lower ∧ (cell13134 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13134 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13134 ⟨46,by decide⟩).lower ∧ (cell13134 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13134 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13134 ⟨47,by decide⟩).lower ∧ (cell13134 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13134 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13134 ⟨48,by decide⟩).lower ∧ (cell13134 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13134 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13134 ⟨49,by decide⟩).lower ∧ (cell13134 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13134 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13134 ⟨50,by decide⟩).lower ∧ (cell13134 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13134 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13134 ⟨51,by decide⟩).lower ∧ (cell13134 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13134 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13134 ⟨52,by decide⟩).lower ∧ (cell13134 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13134 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13134 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13134 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13134,cell13134,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13134 i).lower ∧
    (cell13134 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13134 i).upper ≤ (0.532 : ℝ) ∧
    (cell13134 i).centre ≤ (0.1 : ℝ) ∧ (cell13134 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13134 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13134 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13134

/-! The local source numeric instances at 13134 have no network premises. -/
namespace BstLean.Part269.N13134
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13134)
open BstLean.Part268 (cell13134)

noncomputable def sourceNumerics13134 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13134 (cell13134 i)
      scalarRow13134.M scalarRow13134.H scalarRow13134.xi := by
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
    energy_allowance := scalarRow13134.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13134]
    centre_nonneg := (scalarRow13134.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13134])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13134
/-! Actual 13135 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13135
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13135 ≤ (1.035206099016 : ℝ) := by
  have hr : (114.608027642046 : ℝ) ≤ √(13135 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.608027642046 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13135 13135 (11 / 1000) ≤
    (0.008340488246 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13135) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.608027642046 : ℝ) ≤ √(13135 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13135)
  have hdiv : K / √(13135 : ℝ) ≤ K / 114.608027642046 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.608027642046 ≤ (0.008340488246 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13135.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13135 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13135 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13135 := gPlus_lower 13135
end BstLean.Part269.N13135

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13135
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035206099015 : ℝ) ≤ wn 13135 := by
  have hn : √(13135 : ℝ) ≤ 114.608027642047 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13135 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.608027642047 ≤ 2 / √(13135 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243397367 : ℝ) ≤ rhoBar 13135 BstLean.Part154.csC ∧
    rhoBar 13135 BstLean.Part154.csC ≤ 0.000243397744 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035206099015 : ℝ) / (1.295212 * 13135) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035206099016 : ℝ) / (1.29521 * 13135) := by gcongr
      _ ≤ (0.000243397744 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13135 BstLean.Part154.csC) ≤ 0.000973650219 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13135 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13135 BstLean.Part154.csC) (piBar (rhoBar 13135 BstLean.Part154.csC)) ≤ 0.000185908548 ∧
    cc1 (rhoBar 13135 BstLean.Part154.csC) (piBar (rhoBar 13135 BstLean.Part154.csC)) ≤ 0.000118294903 ∧
    cc2 (rhoBar 13135 BstLean.Part154.csC) ≤ 0.000068671170 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13135 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13135 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13135 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13135 BstLean.Part154.csC * nuR (rhoBar 13135 BstLean.Part154.csC)) ≤ 0.000486810299 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243397744 : ℝ) * 0.000973650219 := by gcongr
      _ ≤ (0.000486810299 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13135 BstLean.Part154.csC) * nuR (rhoBar 13135 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000973650219 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13135 BstLean.Part154.csC) * rhoBar 13135 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243397744 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243397744 / 2 + 0.399 * 0.000973650219 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185908548 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486810299 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118294903 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243397744 / 1.414213562 := by gcongr
      _ ≤ (0.000068671170 : ℝ) := by norm_num

end BstLean.Part269.N13135

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13135
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13135 BstLean.Part154.csC) (piBar (rhoBar 13135 BstLean.Part154.csC)) ≤ 1.49257E-7 := by
  have hr0 : 0 ≤ rhoBar 13135 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13135 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13135 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13135 BstLean.Part154.csC) (piBar (rhoBar 13135 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13135 BstLean.Part154.csC) (piBar (rhoBar 13135 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13135 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185908548 : ℝ) ^ 2 + 0.000118294903 ^ 2 + 3 * 0.000068671170 ^ 2 +
        2 * 0.797885 * 0.000185908548 * 0.000118294903 + 2 * 0.000185908548 * 0.000068671170 +
        4 * 0.797885 * 0.000118294903 * 0.000068671170 := by gcongr
    _ ≤ (1.49257E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13135 BstLean.Part154.csC Θ ≤ 0.002539251080 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13135 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13135 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13135 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13135 BstLean.Part154.csC) (piBar (rhoBar 13135 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13135 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035206099016 * 1.49257E-7 / (0.000243397367 : ℝ) := by gcongr
    _ ≤ 0.002539251080 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13135 BstLean.Part154.csC Θ ≤ 0.002815792329 + 0.000641628395 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13135 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13135 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13135 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035206099016 : ℝ) * ((2 * Θ * 0.000243397744 +
        (6863 / 10000) * 0.000243397744 * 13135 * 0.000973650219) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002815792329 + 0.000641628395 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13135 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13135 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13135 0.011 Θ ∧ gammaRatio 13135 0.011 Θ ≤ 0.000083673851 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13135 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035206099016 : ℝ) * 0.525 / ((1 - 0.011) * 13135) := by gcongr
      _ ≤ (0.000083673851 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13135 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13135 0.011 Θ) :=
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
    badAllowance 13135 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13135 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13135 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13135 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13135 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13135 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13135 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13135 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13135 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13135 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13135 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035206099016 : ℝ) * 13135 *
        (1.2470E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13135 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003164880815 + 0.003180879475 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13135

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13135
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13135 BstLean.Part154.csC) (piBar (rhoBar 13135 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13135 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13135 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13135 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13135 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13135 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13135 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13135 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13135 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13135 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13135 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13135 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13135 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13135 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13135 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051598573318 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13135) ≤ 0.010420191375 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13135 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035206099016)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010420191375 + 2 * 0.737676 / 13135) := by gcongr
    _ ≤ (0.051598573318 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13135 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13135

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13135
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522588793 : ℝ) ≤ plow 13135 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13135) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052341442540)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333106817) : eMP 13135 0.011 xi bn ≤ 0.001148255147 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13135 : ℝ) * (1 - 0.011))) ≤ 0.000567798513 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001333106817 / (13135 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567798513 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567798513 : ℝ) + 3.141593 * 0.052341442540 / (13135 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001148255147 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052341442540)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333106817) : PiBarMP 13135 12 0.011 xi bn ≤ 0.158532153409 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13135 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036511735333 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.975940443586 : ℝ) ≤ √((13135 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.608027642046 : ℝ) ≤ √(13135 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13135) ≤ 0.121565727545 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036511735333 + 0.052341442540 * 1.772454 / (2 * (113.975940443586 : ℝ))) * (1 + 0.001148255147) +
        8 / (13135 * 114.608027642046) + 0.121565727545 := by gcongr
    _ ≤ (0.158532153409 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052341442540)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333106817) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280381095684) :
    parallelOracle 13135 0.011 xi bn cd ≤ 0.159489985241 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13135 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13135 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522588793 : ℝ) ≤ plow 13135 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.608027642046 : ℝ) ≤ √(13135 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280381095684 : ℝ) / (2 * 0.560522588793 * 114.608027642046)) * 0.158532153409 +
        0.280381095684 ^ 2 / (2 * 0.560522588793 * 114.608027642046) := by gcongr
    _ ≤ (0.159489985241 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052341442540) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333106817)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280381095684) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13135 13135 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522588793 : ℝ) ≤ plow 13135 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.608027642046 : ℝ) ≤ √(13135 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13135 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13135 Θ 1.22 ≤ 0.011570747070 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.608027642046 := by gcongr <;> linarith
      _ ≤ (0.011570747070 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13135 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13135 13135 0.011 ≤ 0.008340488246 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13135 13135 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13135 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13135 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13135 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13135 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159489985241 + 0.011570747070 + (0.008340488246 : ℝ) *
        (1 + 2 * (0.280381095684 + 0.011570747070) / (0.560522588793 * 114.608027642046))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13135]

end BstLean.Part269.N13135

/-! The original eight local profiles supply actual 13135 moment certificates. -/
namespace BstLean.Part269.N13135
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13135 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13135 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13135 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052341442540 ∧
    0 ≤ bN 13135 BstLean.Part154.csC (groupTheta g) ∧ bN 13135 BstLean.Part154.csC (groupTheta g) ≤ 0.001333106817 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13135 13135 0.011
      (momentAllowance 13135 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13135 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13135 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13135 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13135 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13135 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228782522366 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13135 0.011
      (momentAllowance 13135 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13135 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13135
/-! The actual computed-centre upper energy formula at 13135. -/
namespace BstLean.Part269.N13135
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13135

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13135
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13135)
open BstLean.Part268 (cell13135)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084313667426
  | 2 => 0.085237920483
  | 3 => 0.086157731741
  | 4 => 0.087073911686
  | 5 => 0.087987457885
  | 6 => 0.088899584872
  | 7 => 0.089811757245
  | 8 => 0.090725726098
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13135 13135 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13135 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13135

/-! Actual upper energy certificates on all 43 source endpoints at 13135. -/
namespace BstLean.Part269.N13135
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13135)
open BstLean.Part268 (cell13135)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13135 (gMinus 13135) (1 - (cell13135 i).lower) ≤ 1 ∧
    energyUpper 13135 (gMinus 13135) (BstLean.Part211.gPlus 13135)
      (finiteEnergy 13135 13135 0.011) (1 - (cell13135 i).lower) ≤
      (cell13135 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨10,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨11,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨12,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨13,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨14,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨15,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨16,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨17,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨18,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨19,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨20,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨21,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨22,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨23,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨24,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨25,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨26,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨27,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨28,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨29,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨30,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨31,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨32,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨33,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨34,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨35,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨36,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨37,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨38,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨39,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨40,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨41,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨42,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨43,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨44,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨45,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨46,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨47,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨48,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨49,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨50,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨51,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13135) (by norm_num)
        (q := 1 - (cell13135 ⟨52,by decide⟩).lower)
        (by norm_num [cell13135]) (by norm_num [cell13135])
      exact ⟨E.1,E.2.trans (by norm_num [cell13135])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13135

/-! Source-cell containment and simple scalar guards at 13135. -/
namespace BstLean.Part269.N13135
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13135)
open BstLean.Part268 (cell13135)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13135 ⟨10,by decide⟩).lower ∧ (cell13135 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13135 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13135 ⟨11,by decide⟩).lower ∧ (cell13135 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13135 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13135 ⟨12,by decide⟩).lower ∧ (cell13135 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13135 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13135 ⟨13,by decide⟩).lower ∧ (cell13135 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13135 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13135 ⟨14,by decide⟩).lower ∧ (cell13135 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13135 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13135 ⟨15,by decide⟩).lower ∧ (cell13135 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13135 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13135 ⟨16,by decide⟩).lower ∧ (cell13135 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13135 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13135 ⟨17,by decide⟩).lower ∧ (cell13135 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13135 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13135 ⟨18,by decide⟩).lower ∧ (cell13135 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13135 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13135 ⟨19,by decide⟩).lower ∧ (cell13135 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13135 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13135 ⟨20,by decide⟩).lower ∧ (cell13135 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13135 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13135 ⟨21,by decide⟩).lower ∧ (cell13135 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13135 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13135 ⟨22,by decide⟩).lower ∧ (cell13135 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13135 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13135 ⟨23,by decide⟩).lower ∧ (cell13135 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13135 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13135 ⟨24,by decide⟩).lower ∧ (cell13135 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13135 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13135 ⟨25,by decide⟩).lower ∧ (cell13135 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13135 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13135 ⟨26,by decide⟩).lower ∧ (cell13135 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13135 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13135 ⟨27,by decide⟩).lower ∧ (cell13135 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13135 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13135 ⟨28,by decide⟩).lower ∧ (cell13135 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13135 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13135 ⟨29,by decide⟩).lower ∧ (cell13135 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13135 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13135 ⟨30,by decide⟩).lower ∧ (cell13135 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13135 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13135 ⟨31,by decide⟩).lower ∧ (cell13135 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13135 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13135 ⟨32,by decide⟩).lower ∧ (cell13135 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13135 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13135 ⟨33,by decide⟩).lower ∧ (cell13135 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13135 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13135 ⟨34,by decide⟩).lower ∧ (cell13135 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13135 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13135 ⟨35,by decide⟩).lower ∧ (cell13135 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13135 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13135 ⟨36,by decide⟩).lower ∧ (cell13135 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13135 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13135 ⟨37,by decide⟩).lower ∧ (cell13135 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13135 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13135 ⟨38,by decide⟩).lower ∧ (cell13135 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13135 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13135 ⟨39,by decide⟩).lower ∧ (cell13135 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13135 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13135 ⟨40,by decide⟩).lower ∧ (cell13135 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13135 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13135 ⟨41,by decide⟩).lower ∧ (cell13135 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13135 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13135 ⟨42,by decide⟩).lower ∧ (cell13135 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13135 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13135 ⟨43,by decide⟩).lower ∧ (cell13135 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13135 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13135 ⟨44,by decide⟩).lower ∧ (cell13135 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13135 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13135 ⟨45,by decide⟩).lower ∧ (cell13135 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13135 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13135 ⟨46,by decide⟩).lower ∧ (cell13135 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13135 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13135 ⟨47,by decide⟩).lower ∧ (cell13135 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13135 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13135 ⟨48,by decide⟩).lower ∧ (cell13135 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13135 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13135 ⟨49,by decide⟩).lower ∧ (cell13135 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13135 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13135 ⟨50,by decide⟩).lower ∧ (cell13135 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13135 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13135 ⟨51,by decide⟩).lower ∧ (cell13135 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13135 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13135 ⟨52,by decide⟩).lower ∧ (cell13135 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13135 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13135 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13135 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13135,cell13135,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13135 i).lower ∧
    (cell13135 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13135 i).upper ≤ (0.532 : ℝ) ∧
    (cell13135 i).centre ≤ (0.1 : ℝ) ∧ (cell13135 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13135 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13135 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13135

/-! The local source numeric instances at 13135 have no network premises. -/
namespace BstLean.Part269.N13135
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13135)
open BstLean.Part268 (cell13135)

noncomputable def sourceNumerics13135 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13135 (cell13135 i)
      scalarRow13135.M scalarRow13135.H scalarRow13135.xi := by
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
    energy_allowance := scalarRow13135.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13135]
    centre_nonneg := (scalarRow13135.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13135])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13135
/-! Actual 13136 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13136
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13136 ≤ (1.035204747338 : ℝ) := by
  have hr : (114.612390255155 : ℝ) ≤ √(13136 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.612390255155 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13136 13136 (11 / 1000) ≤
    (0.008340170771 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13136) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.612390255155 : ℝ) ≤ √(13136 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13136)
  have hdiv : K / √(13136 : ℝ) ≤ K / 114.612390255155 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.612390255155 ≤ (0.008340170771 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13136.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13136 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13136 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13136 := gPlus_lower 13136
end BstLean.Part269.N13136

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13136
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035204747337 : ℝ) ≤ wn 13136 := by
  have hn : √(13136 : ℝ) ≤ 114.612390255156 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13136 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.612390255156 ≤ 2 / √(13136 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243378520 : ℝ) ≤ rhoBar 13136 BstLean.Part154.csC ∧
    rhoBar 13136 BstLean.Part154.csC ≤ 0.000243378897 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035204747337 : ℝ) / (1.295212 * 13136) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035204747338 : ℝ) / (1.29521 * 13136) := by gcongr
      _ ≤ (0.000243378897 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13136 BstLean.Part154.csC) ≤ 0.000973574822 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13136 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13136 BstLean.Part154.csC) (piBar (rhoBar 13136 BstLean.Part154.csC)) ≤ 0.000185894152 ∧
    cc1 (rhoBar 13136 BstLean.Part154.csC) (piBar (rhoBar 13136 BstLean.Part154.csC)) ≤ 0.000118285743 ∧
    cc2 (rhoBar 13136 BstLean.Part154.csC) ≤ 0.000068665853 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13136 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13136 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13136 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13136 BstLean.Part154.csC * nuR (rhoBar 13136 BstLean.Part154.csC)) ≤ 0.000486772603 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243378897 : ℝ) * 0.000973574822 := by gcongr
      _ ≤ (0.000486772603 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13136 BstLean.Part154.csC) * nuR (rhoBar 13136 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000973574822 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13136 BstLean.Part154.csC) * rhoBar 13136 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243378897 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243378897 / 2 + 0.399 * 0.000973574822 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185894152 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486772603 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118285743 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243378897 / 1.414213562 := by gcongr
      _ ≤ (0.000068665853 : ℝ) := by norm_num

end BstLean.Part269.N13136

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13136
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13136 BstLean.Part154.csC) (piBar (rhoBar 13136 BstLean.Part154.csC)) ≤ 1.49234E-7 := by
  have hr0 : 0 ≤ rhoBar 13136 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13136 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13136 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13136 BstLean.Part154.csC) (piBar (rhoBar 13136 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13136 BstLean.Part154.csC) (piBar (rhoBar 13136 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13136 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185894152 : ℝ) ^ 2 + 0.000118285743 ^ 2 + 3 * 0.000068665853 ^ 2 +
        2 * 0.797885 * 0.000185894152 * 0.000118285743 + 2 * 0.000185894152 * 0.000068665853 +
        4 * 0.797885 * 0.000118285743 * 0.000068665853 := by gcongr
    _ ≤ (1.49234E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13136 BstLean.Part154.csC Θ ≤ 0.002539053082 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13136 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13136 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13136 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13136 BstLean.Part154.csC) (piBar (rhoBar 13136 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13136 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035204747338 * 1.49234E-7 / (0.000243378520 : ℝ) := by gcongr
    _ ≤ 0.002539053082 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13136 BstLean.Part154.csC Θ ≤ 0.002815566927 + 0.000641577875 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13136 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13136 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13136 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035204747338 : ℝ) * ((2 * Θ * 0.000243378897 +
        (6863 / 10000) * 0.000243378897 * 13136 * 0.000973574822) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002815566927 + 0.000641577875 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13136 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13136 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13136 0.011 Θ ∧ gammaRatio 13136 0.011 Θ ≤ 0.000083667371 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13136 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035204747338 : ℝ) * 0.525 / ((1 - 0.011) * 13136) := by gcongr
      _ ≤ (0.000083667371 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13136 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13136 0.011 Θ) :=
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
    badAllowance 13136 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13136 BstLean.Part154.csC) 1.22 ≤ 1.2470E-8 := by
    have he : (18.2 : ℝ) ≤ gap 2 (rhoBar 13136 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13136 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13136 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_2_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13136 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13136 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13136 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13136 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13136 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13136 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035204747338 : ℝ) * 13136 *
        (1.2470E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13136 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003164655413 + 0.003180630957 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13136

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13136
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13136 BstLean.Part154.csC) (piBar (rhoBar 13136 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13136 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13136 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13136 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13136 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13136 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13136 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13136 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13136 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13136 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13136 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13136 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13136 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13136 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13136 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051596588321 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13136) ≤ 0.010419794740 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13136 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035204747338)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010419794740 + 2 * 0.737676 / 13136) := by gcongr
    _ ≤ (0.051596588321 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13136 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13136

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13136
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522631067 : ℝ) ≤ plow 13136 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13136) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052341086666)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333002869) : eMP 13136 0.011 xi bn ≤ 0.001148166600 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13136 : ℝ) * (1 - 0.011))) ≤ 0.000567754764 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001333002869 / (13136 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567754764 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567754764 : ℝ) + 3.141593 * 0.052341086666 / (13136 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001148166600 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052341086666)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333002869) : PiBarMP 13136 12 0.011 xi bn ≤ 0.158526078819 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13136 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036510311818 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.980278995973 : ℝ) ≤ √((13136 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.612390255155 : ℝ) ≤ √(13136 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13136) ≤ 0.121561100260 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036510311818 + 0.052341086666 * 1.772454 / (2 * (113.980278995973 : ℝ))) * (1 + 0.001148166600) +
        8 / (13136 * 114.612390255155) + 0.121561100260 := by gcongr
    _ ≤ (0.158526078819 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052341086666)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333002869) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280378332930) :
    parallelOracle 13136 0.011 xi bn cd ≤ 0.159483845398 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13136 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13136 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522631067 : ℝ) ≤ plow 13136 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.612390255155 : ℝ) ≤ √(13136 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280378332930 : ℝ) / (2 * 0.560522631067 * 114.612390255155)) * 0.158526078819 +
        0.280378332930 ^ 2 / (2 * 0.560522631067 * 114.612390255155) := by gcongr
    _ ≤ (0.159483845398 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052341086666) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001333002869)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280378332930) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13136 13136 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522631067 : ℝ) ≤ plow 13136 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.612390255155 : ℝ) ≤ √(13136 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13136 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13136 Θ 1.22 ≤ 0.011570306641 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.612390255155 := by gcongr <;> linarith
      _ ≤ (0.011570306641 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13136 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13136 13136 0.011 ≤ 0.008340170771 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13136 13136 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13136 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13136 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13136 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13136 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159483845398 + 0.011570306641 + (0.008340170771 : ℝ) *
        (1 + 2 * (0.280378332930 + 0.011570306641) / (0.560522631067 * 114.612390255155))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13136]

end BstLean.Part269.N13136

/-! The original eight local profiles supply actual 13136 moment certificates. -/
namespace BstLean.Part269.N13136
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13136 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13136 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13136 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052341086666 ∧
    0 ≤ bN 13136 BstLean.Part154.csC (groupTheta g) ∧ bN 13136 BstLean.Part154.csC (groupTheta g) ≤ 0.001333002869 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13136 13136 0.011
      (momentAllowance 13136 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13136 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13136 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13136 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13136 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13136 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228781744609 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13136 0.011
      (momentAllowance 13136 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13136 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13136
/-! The actual computed-centre upper energy formula at 13136. -/
namespace BstLean.Part269.N13136
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13136

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13136
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13136)
open BstLean.Part268 (cell13136)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084311151761
  | 2 => 0.085235373804
  | 3 => 0.086155149644
  | 4 => 0.087071288715
  | 5 => 0.087984787337
  | 6 => 0.088896858572
  | 7 => 0.089808965299
  | 8 => 0.090722856608
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13136 13136 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13136 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13136

/-! Actual upper energy certificates on all 43 source endpoints at 13136. -/
namespace BstLean.Part269.N13136
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13136)
open BstLean.Part268 (cell13136)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13136 (gMinus 13136) (1 - (cell13136 i).lower) ≤ 1 ∧
    energyUpper 13136 (gMinus 13136) (BstLean.Part211.gPlus 13136)
      (finiteEnergy 13136 13136 0.011) (1 - (cell13136 i).lower) ≤
      (cell13136 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨10,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨11,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨12,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨13,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨14,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨15,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨16,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨17,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨18,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨19,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨20,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨21,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨22,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨23,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨24,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨25,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨26,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨27,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨28,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨29,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨30,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨31,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨32,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨33,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨34,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨35,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨36,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨37,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨38,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨39,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨40,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨41,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨42,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨43,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨44,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨45,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨46,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨47,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨48,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨49,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨50,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨51,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13136) (by norm_num)
        (q := 1 - (cell13136 ⟨52,by decide⟩).lower)
        (by norm_num [cell13136]) (by norm_num [cell13136])
      exact ⟨E.1,E.2.trans (by norm_num [cell13136])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13136

/-! Source-cell containment and simple scalar guards at 13136. -/
namespace BstLean.Part269.N13136
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13136)
open BstLean.Part268 (cell13136)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13136 ⟨10,by decide⟩).lower ∧ (cell13136 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13136 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13136 ⟨11,by decide⟩).lower ∧ (cell13136 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13136 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13136 ⟨12,by decide⟩).lower ∧ (cell13136 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13136 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13136 ⟨13,by decide⟩).lower ∧ (cell13136 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13136 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13136 ⟨14,by decide⟩).lower ∧ (cell13136 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13136 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13136 ⟨15,by decide⟩).lower ∧ (cell13136 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13136 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13136 ⟨16,by decide⟩).lower ∧ (cell13136 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13136 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13136 ⟨17,by decide⟩).lower ∧ (cell13136 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13136 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13136 ⟨18,by decide⟩).lower ∧ (cell13136 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13136 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13136 ⟨19,by decide⟩).lower ∧ (cell13136 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13136 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13136 ⟨20,by decide⟩).lower ∧ (cell13136 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13136 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13136 ⟨21,by decide⟩).lower ∧ (cell13136 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13136 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13136 ⟨22,by decide⟩).lower ∧ (cell13136 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13136 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13136 ⟨23,by decide⟩).lower ∧ (cell13136 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13136 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13136 ⟨24,by decide⟩).lower ∧ (cell13136 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13136 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13136 ⟨25,by decide⟩).lower ∧ (cell13136 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13136 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13136 ⟨26,by decide⟩).lower ∧ (cell13136 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13136 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13136 ⟨27,by decide⟩).lower ∧ (cell13136 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13136 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13136 ⟨28,by decide⟩).lower ∧ (cell13136 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13136 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13136 ⟨29,by decide⟩).lower ∧ (cell13136 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13136 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13136 ⟨30,by decide⟩).lower ∧ (cell13136 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13136 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13136 ⟨31,by decide⟩).lower ∧ (cell13136 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13136 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13136 ⟨32,by decide⟩).lower ∧ (cell13136 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13136 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13136 ⟨33,by decide⟩).lower ∧ (cell13136 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13136 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13136 ⟨34,by decide⟩).lower ∧ (cell13136 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13136 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13136 ⟨35,by decide⟩).lower ∧ (cell13136 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13136 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13136 ⟨36,by decide⟩).lower ∧ (cell13136 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13136 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13136 ⟨37,by decide⟩).lower ∧ (cell13136 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13136 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13136 ⟨38,by decide⟩).lower ∧ (cell13136 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13136 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13136 ⟨39,by decide⟩).lower ∧ (cell13136 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13136 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13136 ⟨40,by decide⟩).lower ∧ (cell13136 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13136 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13136 ⟨41,by decide⟩).lower ∧ (cell13136 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13136 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13136 ⟨42,by decide⟩).lower ∧ (cell13136 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13136 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13136 ⟨43,by decide⟩).lower ∧ (cell13136 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13136 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13136 ⟨44,by decide⟩).lower ∧ (cell13136 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13136 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13136 ⟨45,by decide⟩).lower ∧ (cell13136 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13136 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13136 ⟨46,by decide⟩).lower ∧ (cell13136 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13136 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13136 ⟨47,by decide⟩).lower ∧ (cell13136 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13136 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13136 ⟨48,by decide⟩).lower ∧ (cell13136 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13136 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13136 ⟨49,by decide⟩).lower ∧ (cell13136 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13136 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13136 ⟨50,by decide⟩).lower ∧ (cell13136 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13136 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13136 ⟨51,by decide⟩).lower ∧ (cell13136 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13136 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13136 ⟨52,by decide⟩).lower ∧ (cell13136 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13136 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13136 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13136 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13136,cell13136,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13136 i).lower ∧
    (cell13136 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13136 i).upper ≤ (0.532 : ℝ) ∧
    (cell13136 i).centre ≤ (0.1 : ℝ) ∧ (cell13136 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13136 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13136 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13136

/-! The local source numeric instances at 13136 have no network premises. -/
namespace BstLean.Part269.N13136
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13136)
open BstLean.Part268 (cell13136)

noncomputable def sourceNumerics13136 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13136 (cell13136 i)
      scalarRow13136.M scalarRow13136.H scalarRow13136.xi := by
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
    energy_allowance := scalarRow13136.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13136]
    centre_nonneg := (scalarRow13136.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13136])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13136
/-! Actual 13137 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13137
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13137 ≤ (1.035203395815 : ℝ) := by
  have hr : (114.616752702211 : ℝ) ≤ √(13137 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.616752702211 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13137 13137 (11 / 1000) ≤
    (0.008339853332 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13137) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.616752702211 : ℝ) ≤ √(13137 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13137)
  have hdiv : K / √(13137 : ℝ) ≤ K / 114.616752702211 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.616752702211 ≤ (0.008339853332 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13137.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13137 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13137 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13137 := gPlus_lower 13137
end BstLean.Part269.N13137

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13137
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035203395814 : ℝ) ≤ wn 13137 := by
  have hn : √(13137 : ℝ) ≤ 114.616752702212 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13137 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.616752702212 ≤ 2 / √(13137 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243359676 : ℝ) ≤ rhoBar 13137 BstLean.Part154.csC ∧
    rhoBar 13137 BstLean.Part154.csC ≤ 0.000243360053 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035203395814 : ℝ) / (1.295212 * 13137) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035203395815 : ℝ) / (1.29521 * 13137) := by gcongr
      _ ≤ (0.000243360053 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13137 BstLean.Part154.csC) ≤ 0.000973499437 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13137 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13137 BstLean.Part154.csC) (piBar (rhoBar 13137 BstLean.Part154.csC)) ≤ 0.000185879758 ∧
    cc1 (rhoBar 13137 BstLean.Part154.csC) (piBar (rhoBar 13137 BstLean.Part154.csC)) ≤ 0.000118276584 ∧
    cc2 (rhoBar 13137 BstLean.Part154.csC) ≤ 0.000068660536 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13137 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13137 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13137 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13137 BstLean.Part154.csC * nuR (rhoBar 13137 BstLean.Part154.csC)) ≤ 0.000486734913 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243360053 : ℝ) * 0.000973499437 := by gcongr
      _ ≤ (0.000486734913 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13137 BstLean.Part154.csC) * nuR (rhoBar 13137 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000973499437 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13137 BstLean.Part154.csC) * rhoBar 13137 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243360053 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243360053 / 2 + 0.399 * 0.000973499437 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185879758 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486734913 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118276584 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243360053 / 1.414213562 := by gcongr
      _ ≤ (0.000068660536 : ℝ) := by norm_num

end BstLean.Part269.N13137

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13137
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13137 BstLean.Part154.csC) (piBar (rhoBar 13137 BstLean.Part154.csC)) ≤ 1.49211E-7 := by
  have hr0 : 0 ≤ rhoBar 13137 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13137 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13137 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13137 BstLean.Part154.csC) (piBar (rhoBar 13137 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13137 BstLean.Part154.csC) (piBar (rhoBar 13137 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13137 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185879758 : ℝ) ^ 2 + 0.000118276584 ^ 2 + 3 * 0.000068660536 ^ 2 +
        2 * 0.797885 * 0.000185879758 * 0.000118276584 + 2 * 0.000185879758 * 0.000068660536 +
        4 * 0.797885 * 0.000118276584 * 0.000068660536 := by gcongr
    _ ≤ (1.49211E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13137 BstLean.Part154.csC Θ ≤ 0.002538855023 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13137 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13137 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13137 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13137 BstLean.Part154.csC) (piBar (rhoBar 13137 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13137 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035203395815 * 1.49211E-7 / (0.000243359676 : ℝ) := by gcongr
    _ ≤ 0.002538855023 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13137 BstLean.Part154.csC Θ ≤ 0.002815341563 + 0.000641527362 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13137 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13137 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13137 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035203395815 : ℝ) * ((2 * Θ * 0.000243360053 +
        (6863 / 10000) * 0.000243360053 * 13137 * 0.000973499437) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002815341563 + 0.000641527362 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13137 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13137 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13137 0.011 Θ ∧ gammaRatio 13137 0.011 Θ ≤ 0.000083660893 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13137 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035203395815 : ℝ) * 0.525 / ((1 - 0.011) * 13137) := by gcongr
      _ ≤ (0.000083660893 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13137 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13137 0.011 Θ) :=
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
    badAllowance 13137 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000349088486 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13137 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13137 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13137 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13137 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13137 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13137 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13137 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13137 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13137 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13137 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035203395815 : ℝ) * 13137 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000349088486 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13137 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003164430049 + 0.003180382385 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13137

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13137
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13137 BstLean.Part154.csC) (piBar (rhoBar 13137 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13137 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13137 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13137 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13137 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13137 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13137 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13137 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13137 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13137 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13137 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13137 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13137 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13137 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13137 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051594603551 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13137) ≤ 0.010419398150 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13137 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035203395815)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010419398150 + 2 * 0.737676 / 13137) := by gcongr
    _ ≤ (0.051594603551 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13137 12 ≤ 0.0015 := by
  exact BstLean.Part269.S31.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13137

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13137
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560522673334 : ℝ) ≤ plow 13137 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13137) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052340730802)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332898888) : eMP 13137 0.011 xi bn ≤ 0.001148078044 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13137 : ℝ) * (1 - 0.011))) ≤ 0.000567711011 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001332898888 / (13137 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567711011 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567711011 : ℝ) + 3.141593 * 0.052340730802 / (13137 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001148078044 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052340730802)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332898888) : PiBarMP 13137 12 0.011 xi bn ≤ 0.158520004251 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13137 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036508887795 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (113.984617383224 : ℝ) ≤ √((13137 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.616752702211 : ℝ) ≤ √(13137 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13137) ≤ 0.121556473503 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036508887795 + 0.052340730802 * 1.772454 / (2 * (113.984617383224 : ℝ))) * (1 + 0.001148078044) +
        8 / (13137 * 114.616752702211) + 0.121556473503 := by gcongr
    _ ≤ (0.158520004251 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052340730802)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332898888) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280375570422) :
    parallelOracle 13137 0.011 xi bn cd ≤ 0.159477705584 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13137 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13137 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560522673334 : ℝ) ≤ plow 13137 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.616752702211 : ℝ) ≤ √(13137 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280375570422 : ℝ) / (2 * 0.560522673334 * 114.616752702211)) * 0.158520004251 +
        0.280375570422 ^ 2 / (2 * 0.560522673334 * 114.616752702211) := by gcongr
    _ ≤ (0.159477705584 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052340730802) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001332898888)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280375570422) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13137 13137 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560522673334 : ℝ) ≤ plow 13137 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.616752702211 : ℝ) ≤ √(13137 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13137 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13137 Θ 1.22 ≤ 0.011569866261 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.616752702211 := by gcongr <;> linarith
      _ ≤ (0.011569866261 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13137 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13137 13137 0.011 ≤ 0.008339853332 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13137 13137 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13137 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13137 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13137 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13137 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159477705584 + 0.011569866261 + (0.008339853332 : ℝ) *
        (1 + 2 * (0.280375570422 + 0.011569866261) / (0.560522673334 * 114.616752702211))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13137]

end BstLean.Part269.N13137

/-! The original eight local profiles supply actual 13137 moment certificates. -/
namespace BstLean.Part269.N13137
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13137 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13137 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13137 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052340730802 ∧
    0 ≤ bN 13137 BstLean.Part154.csC (groupTheta g) ∧ bN 13137 BstLean.Part154.csC (groupTheta g) ≤ 0.001332898888 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13137 13137 0.011
      (momentAllowance 13137 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13137 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13137 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13137 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13137 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13137 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228780966871 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13137 0.011
      (momentAllowance 13137 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13137 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13137
/-! The actual computed-centre upper energy formula at 13137. -/
namespace BstLean.Part269.N13137
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13137

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13137
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13137)
open BstLean.Part268 (cell13137)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084308636810
  | 2 => 0.085232827863
  | 3 => 0.086152568316
  | 4 => 0.087068666550
  | 5 => 0.087982117639
  | 6 => 0.088894133178
  | 7 => 0.089806174325
  | 8 => 0.090719988171
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13137 13137 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13137 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003167136758 + 0.003183378840 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S31.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S31.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13137

/-! Actual upper energy certificates on all 43 source endpoints at 13137. -/
namespace BstLean.Part269.N13137
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13137)
open BstLean.Part268 (cell13137)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13137 (gMinus 13137) (1 - (cell13137 i).lower) ≤ 1 ∧
    energyUpper 13137 (gMinus 13137) (BstLean.Part211.gPlus 13137)
      (finiteEnergy 13137 13137 0.011) (1 - (cell13137 i).lower) ≤
      (cell13137 i).energy := by
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
      have E := BstLean.Part269.S31.uniformEnergy10 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨10,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy11 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨11,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy12 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨12,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy13 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨13,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy14 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨14,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy15 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨15,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy16 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨16,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy17 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨17,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy18 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨18,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy19 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨19,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy20 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨20,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy21 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨21,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy22 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨22,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy23 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨23,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy24 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨24,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy25 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨25,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy26 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨26,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy27 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨27,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy28 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨28,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy29 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨29,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy30 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨30,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy31 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨31,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy32 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨32,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy33 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨33,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy34 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨34,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy35 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨35,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy36 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨36,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy37 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨37,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy38 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨38,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy39 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨39,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy40 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨40,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy41 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨41,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy42 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨42,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy43 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨43,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy44 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨44,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy45 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨45,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy46 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨46,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy47 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨47,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy48 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨48,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy49 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨49,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy50 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨50,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy51 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨51,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S31.uniformEnergy52 (n := 13137) (by norm_num)
        (q := 1 - (cell13137 ⟨52,by decide⟩).lower)
        (by norm_num [cell13137]) (by norm_num [cell13137])
      exact ⟨E.1,E.2.trans (by norm_num [cell13137])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13137

/-! Source-cell containment and simple scalar guards at 13137. -/
namespace BstLean.Part269.N13137
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13137)
open BstLean.Part268 (cell13137)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13137 ⟨10,by decide⟩).lower ∧ (cell13137 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13137 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13137 ⟨11,by decide⟩).lower ∧ (cell13137 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13137 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13137 ⟨12,by decide⟩).lower ∧ (cell13137 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13137 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13137 ⟨13,by decide⟩).lower ∧ (cell13137 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13137 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13137 ⟨14,by decide⟩).lower ∧ (cell13137 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13137 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13137 ⟨15,by decide⟩).lower ∧ (cell13137 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13137 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13137 ⟨16,by decide⟩).lower ∧ (cell13137 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13137 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13137 ⟨17,by decide⟩).lower ∧ (cell13137 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13137 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13137 ⟨18,by decide⟩).lower ∧ (cell13137 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13137 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13137 ⟨19,by decide⟩).lower ∧ (cell13137 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13137 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13137 ⟨20,by decide⟩).lower ∧ (cell13137 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13137 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13137 ⟨21,by decide⟩).lower ∧ (cell13137 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13137 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13137 ⟨22,by decide⟩).lower ∧ (cell13137 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13137 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13137 ⟨23,by decide⟩).lower ∧ (cell13137 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13137 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13137 ⟨24,by decide⟩).lower ∧ (cell13137 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13137 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13137 ⟨25,by decide⟩).lower ∧ (cell13137 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13137 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13137 ⟨26,by decide⟩).lower ∧ (cell13137 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13137 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13137 ⟨27,by decide⟩).lower ∧ (cell13137 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13137 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13137 ⟨28,by decide⟩).lower ∧ (cell13137 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13137 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13137 ⟨29,by decide⟩).lower ∧ (cell13137 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13137 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13137 ⟨30,by decide⟩).lower ∧ (cell13137 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13137 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13137 ⟨31,by decide⟩).lower ∧ (cell13137 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13137 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13137 ⟨32,by decide⟩).lower ∧ (cell13137 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13137 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13137 ⟨33,by decide⟩).lower ∧ (cell13137 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13137 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13137 ⟨34,by decide⟩).lower ∧ (cell13137 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13137 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13137 ⟨35,by decide⟩).lower ∧ (cell13137 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13137 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13137 ⟨36,by decide⟩).lower ∧ (cell13137 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13137 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13137 ⟨37,by decide⟩).lower ∧ (cell13137 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13137 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13137 ⟨38,by decide⟩).lower ∧ (cell13137 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13137 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13137 ⟨39,by decide⟩).lower ∧ (cell13137 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13137 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13137 ⟨40,by decide⟩).lower ∧ (cell13137 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13137 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13137 ⟨41,by decide⟩).lower ∧ (cell13137 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13137 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13137 ⟨42,by decide⟩).lower ∧ (cell13137 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13137 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13137 ⟨43,by decide⟩).lower ∧ (cell13137 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13137 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13137 ⟨44,by decide⟩).lower ∧ (cell13137 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13137 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13137 ⟨45,by decide⟩).lower ∧ (cell13137 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13137 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13137 ⟨46,by decide⟩).lower ∧ (cell13137 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13137 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13137 ⟨47,by decide⟩).lower ∧ (cell13137 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13137 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13137 ⟨48,by decide⟩).lower ∧ (cell13137 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13137 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13137 ⟨49,by decide⟩).lower ∧ (cell13137 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13137 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13137 ⟨50,by decide⟩).lower ∧ (cell13137 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13137 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13137 ⟨51,by decide⟩).lower ∧ (cell13137 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13137 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13137 ⟨52,by decide⟩).lower ∧ (cell13137 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13137 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13137 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13137 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13137,cell13137,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13137 i).lower ∧
    (cell13137 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13137 i).upper ≤ (0.532 : ℝ) ∧
    (cell13137 i).centre ≤ (0.1 : ℝ) ∧ (cell13137 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13137 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13137 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13137

/-! The local source numeric instances at 13137 have no network premises. -/
namespace BstLean.Part269.N13137
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13137)
open BstLean.Part268 (cell13137)

noncomputable def sourceNumerics13137 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13137 (cell13137 i)
      scalarRow13137.M scalarRow13137.H scalarRow13137.xi := by
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
    energy_allowance := scalarRow13137.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13137]
    centre_nonneg := (scalarRow13137.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D31.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13137])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13137