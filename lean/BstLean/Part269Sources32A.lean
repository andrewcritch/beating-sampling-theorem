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
import BstLean.Part269Direction32
import BstLean.Part269Shared32
import BstLean.Part269Finite
import BstLean.Part269Rows32
import BstLean.Part269Source
/-! Actual 13150 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13150
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13150 ≤ (1.035185840126 : ℝ) := by
  have hr : (114.673449411797 : ℝ) ≤ √(13150 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.673449411797 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13150 13150 (11 / 1000) ≤
    (0.008335729921 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13150) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.673449411797 : ℝ) ≤ √(13150 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13150)
  have hdiv : K / √(13150 : ℝ) ≤ K / 114.673449411797 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.673449411797 ≤ (0.008335729921 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13150.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13150 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13150 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13150 := gPlus_lower 13150
end BstLean.Part269.N13150

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13150
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035185840125 : ℝ) ≤ wn 13150 := by
  have hn : √(13150 : ℝ) ≤ 114.673449411798 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13150 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.673449411798 ≤ 2 / √(13150 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243114970 : ℝ) ≤ rhoBar 13150 BstLean.Part154.csC ∧
    rhoBar 13150 BstLean.Part154.csC ≤ 0.000243115346 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035185840125 : ℝ) / (1.295212 * 13150) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035185840126 : ℝ) / (1.29521 * 13150) := by gcongr
      _ ≤ (0.000243115346 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13150 BstLean.Part154.csC) ≤ 0.000972520490 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13150 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13150 BstLean.Part154.csC) (piBar (rhoBar 13150 BstLean.Part154.csC)) ≤ 0.000185692841 ∧
    cc1 (rhoBar 13150 BstLean.Part154.csC) (piBar (rhoBar 13150 BstLean.Part154.csC)) ≤ 0.000118157649 ∧
    cc2 (rhoBar 13150 BstLean.Part154.csC) ≤ 0.000068591496 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13150 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13150 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13150 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13150 BstLean.Part154.csC * nuR (rhoBar 13150 BstLean.Part154.csC)) ≤ 0.000486245469 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243115346 : ℝ) * 0.000972520490 := by gcongr
      _ ≤ (0.000486245469 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13150 BstLean.Part154.csC) * nuR (rhoBar 13150 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000972520490 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13150 BstLean.Part154.csC) * rhoBar 13150 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243115346 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243115346 / 2 + 0.399 * 0.000972520490 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185692841 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486245469 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118157649 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243115346 / 1.414213562 := by gcongr
      _ ≤ (0.000068591496 : ℝ) := by norm_num

end BstLean.Part269.N13150

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13150
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13150 BstLean.Part154.csC) (piBar (rhoBar 13150 BstLean.Part154.csC)) ≤ 1.48911E-7 := by
  have hr0 : 0 ≤ rhoBar 13150 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13150 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13150 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13150 BstLean.Part154.csC) (piBar (rhoBar 13150 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13150 BstLean.Part154.csC) (piBar (rhoBar 13150 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13150 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185692841 : ℝ) ^ 2 + 0.000118157649 ^ 2 + 3 * 0.000068591496 ^ 2 +
        2 * 0.797885 * 0.000185692841 * 0.000118157649 + 2 * 0.000185692841 * 0.000068591496 +
        4 * 0.797885 * 0.000118157649 * 0.000068591496 := by gcongr
    _ ≤ (1.48911E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13150 BstLean.Part154.csC Θ ≤ 0.002536257782 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13150 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13150 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13150 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13150 BstLean.Part154.csC) (piBar (rhoBar 13150 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13150 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035185840126 * 1.48911E-7 / (0.000243114970 : ℝ) := by gcongr
    _ ≤ 0.002536257782 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13150 BstLean.Part154.csC Θ ≤ 0.002812415075 + 0.000640871415 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13150 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13150 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13150 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035185840126 : ℝ) * ((2 * Θ * 0.000243115346 +
        (6863 / 10000) * 0.000243115346 * 13150 * 0.000972520490) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002812415075 + 0.000640871415 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13150 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13150 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13150 0.011 Θ ∧ gammaRatio 13150 0.011 Θ ≤ 0.000083576769 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13150 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035185840126 : ℝ) * 0.525 / ((1 - 0.011) * 13150) := by gcongr
      _ ≤ (0.000083576769 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13150 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13150 0.011 Θ) :=
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
    badAllowance 13150 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13150 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13150 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13150 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13150 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13150 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13150 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13150 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13150 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13150 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13150 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035185840126 : ℝ) * 13150 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13150 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003129300233 + 0.003177129197 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13150

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13150
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13150 BstLean.Part154.csC) (piBar (rhoBar 13150 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13150 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13150 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13150 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13150 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13150 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13150 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13150 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13150 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13150 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13150 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13150 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13150 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13150 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13150 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051568822326 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13150) ≤ 0.010414246604 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13150 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035185840126)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010414246604 + 2 * 0.737676 / 13150) := by gcongr
    _ ≤ (0.051568822326 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13150 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13150

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13150
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523222228 : ℝ) ≤ plow 13150 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13150) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052303893062)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331535336) : eMP 13150 0.011 xi bn ≤ 0.001146914632 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13150 : ℝ) * (1 - 0.011))) ≤ 0.000567140010 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001331535336 / (13150 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567140010 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567140010 : ℝ) + 3.141593 * 0.052303893062 / (13150 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001146914632 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052303893062)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331535336) : PiBarMP 13150 12 0.011 xi bn ≤ 0.158440665138 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13150 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036490208769 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.041001398619 : ℝ) ≤ √((13150 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.673449411797 : ℝ) ≤ √(13150 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13150) ≤ 0.121496373697 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036490208769 + 0.052303893062 * 1.772454 / (2 * (114.041001398619 : ℝ))) * (1 + 0.001146914632) +
        8 / (13150 * 114.673449411797) + 0.121496373697 := by gcongr
    _ ≤ (0.158440665138 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052303893062)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331535336) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280269266274) :
    parallelOracle 13150 0.011 xi bn cd ≤ 0.159397124364 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13150 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13150 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523222228 : ℝ) ≤ plow 13150 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.673449411797 : ℝ) ≤ √(13150 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280269266274 : ℝ) / (2 * 0.560523222228 * 114.673449411797)) * 0.158440665138 +
        0.280269266274 ^ 2 / (2 * 0.560523222228 * 114.673449411797) := by gcongr
    _ ≤ (0.159397124364 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052303893062) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331535336)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280269266274) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13150 13150 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523222228 : ℝ) ≤ plow 13150 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.673449411797 : ℝ) ≤ √(13150 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13150 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13150 Θ 1.22 ≤ 0.011564145902 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.673449411797 := by gcongr <;> linarith
      _ ≤ (0.011564145902 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13150 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13150 13150 0.011 ≤ 0.008335729921 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13150 13150 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13150 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13150 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13150 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13150 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159397124364 + 0.011564145902 + (0.008335729921 : ℝ) *
        (1 + 2 * (0.280269266274 + 0.011564145902) / (0.560523222228 * 114.673449411797))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13150]

end BstLean.Part269.N13150

/-! The original eight local profiles supply actual 13150 moment certificates. -/
namespace BstLean.Part269.N13150
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13150 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13150 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13150 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052303893062 ∧
    0 ≤ bN 13150 BstLean.Part154.csC (groupTheta g) ∧ bN 13150 BstLean.Part154.csC (groupTheta g) ≤ 0.001331535336 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13150 13150 0.011
      (momentAllowance 13150 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13150 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13150 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13150 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13150 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13150 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228700443948 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13150 0.011
      (momentAllowance 13150 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13150 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13150
/-! The actual computed-centre upper energy formula at 13150. -/
namespace BstLean.Part269.N13150
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13150

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13150
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13150)
open BstLean.Part268 (cell13150)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084276007173
  | 2 => 0.085199797519
  | 3 => 0.086119080616
  | 4 => 0.087034651295
  | 5 => 0.087947488551
  | 6 => 0.088858785033
  | 7 => 0.089769979720
  | 8 => 0.090682793898
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13150 13150 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13150 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13150

/-! Actual upper energy certificates on all 43 source endpoints at 13150. -/
namespace BstLean.Part269.N13150
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13150)
open BstLean.Part268 (cell13150)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13150 (gMinus 13150) (1 - (cell13150 i).lower) ≤ 1 ∧
    energyUpper 13150 (gMinus 13150) (BstLean.Part211.gPlus 13150)
      (finiteEnergy 13150 13150 0.011) (1 - (cell13150 i).lower) ≤
      (cell13150 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨10,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨11,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨12,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨13,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨14,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨15,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨16,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨17,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨18,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨19,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨20,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨21,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨22,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨23,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨24,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨25,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨26,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨27,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨28,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨29,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨30,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨31,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨32,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨33,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨34,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨35,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨36,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨37,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨38,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨39,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨40,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨41,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨42,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨43,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨44,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨45,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨46,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨47,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨48,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨49,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨50,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨51,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13150) (by norm_num)
        (q := 1 - (cell13150 ⟨52,by decide⟩).lower)
        (by norm_num [cell13150]) (by norm_num [cell13150])
      exact ⟨E.1,E.2.trans (by norm_num [cell13150])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13150

/-! Source-cell containment and simple scalar guards at 13150. -/
namespace BstLean.Part269.N13150
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13150)
open BstLean.Part268 (cell13150)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13150 ⟨10,by decide⟩).lower ∧ (cell13150 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13150 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13150 ⟨11,by decide⟩).lower ∧ (cell13150 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13150 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13150 ⟨12,by decide⟩).lower ∧ (cell13150 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13150 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13150 ⟨13,by decide⟩).lower ∧ (cell13150 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13150 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13150 ⟨14,by decide⟩).lower ∧ (cell13150 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13150 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13150 ⟨15,by decide⟩).lower ∧ (cell13150 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13150 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13150 ⟨16,by decide⟩).lower ∧ (cell13150 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13150 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13150 ⟨17,by decide⟩).lower ∧ (cell13150 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13150 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13150 ⟨18,by decide⟩).lower ∧ (cell13150 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13150 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13150 ⟨19,by decide⟩).lower ∧ (cell13150 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13150 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13150 ⟨20,by decide⟩).lower ∧ (cell13150 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13150 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13150 ⟨21,by decide⟩).lower ∧ (cell13150 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13150 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13150 ⟨22,by decide⟩).lower ∧ (cell13150 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13150 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13150 ⟨23,by decide⟩).lower ∧ (cell13150 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13150 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13150 ⟨24,by decide⟩).lower ∧ (cell13150 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13150 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13150 ⟨25,by decide⟩).lower ∧ (cell13150 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13150 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13150 ⟨26,by decide⟩).lower ∧ (cell13150 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13150 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13150 ⟨27,by decide⟩).lower ∧ (cell13150 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13150 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13150 ⟨28,by decide⟩).lower ∧ (cell13150 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13150 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13150 ⟨29,by decide⟩).lower ∧ (cell13150 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13150 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13150 ⟨30,by decide⟩).lower ∧ (cell13150 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13150 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13150 ⟨31,by decide⟩).lower ∧ (cell13150 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13150 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13150 ⟨32,by decide⟩).lower ∧ (cell13150 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13150 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13150 ⟨33,by decide⟩).lower ∧ (cell13150 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13150 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13150 ⟨34,by decide⟩).lower ∧ (cell13150 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13150 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13150 ⟨35,by decide⟩).lower ∧ (cell13150 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13150 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13150 ⟨36,by decide⟩).lower ∧ (cell13150 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13150 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13150 ⟨37,by decide⟩).lower ∧ (cell13150 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13150 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13150 ⟨38,by decide⟩).lower ∧ (cell13150 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13150 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13150 ⟨39,by decide⟩).lower ∧ (cell13150 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13150 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13150 ⟨40,by decide⟩).lower ∧ (cell13150 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13150 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13150 ⟨41,by decide⟩).lower ∧ (cell13150 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13150 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13150 ⟨42,by decide⟩).lower ∧ (cell13150 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13150 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13150 ⟨43,by decide⟩).lower ∧ (cell13150 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13150 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13150 ⟨44,by decide⟩).lower ∧ (cell13150 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13150 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13150 ⟨45,by decide⟩).lower ∧ (cell13150 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13150 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13150 ⟨46,by decide⟩).lower ∧ (cell13150 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13150 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13150 ⟨47,by decide⟩).lower ∧ (cell13150 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13150 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13150 ⟨48,by decide⟩).lower ∧ (cell13150 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13150 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13150 ⟨49,by decide⟩).lower ∧ (cell13150 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13150 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13150 ⟨50,by decide⟩).lower ∧ (cell13150 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13150 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13150 ⟨51,by decide⟩).lower ∧ (cell13150 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13150 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13150 ⟨52,by decide⟩).lower ∧ (cell13150 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13150 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13150 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13150 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13150,cell13150,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13150 i).lower ∧
    (cell13150 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13150 i).upper ≤ (0.532 : ℝ) ∧
    (cell13150 i).centre ≤ (0.1 : ℝ) ∧ (cell13150 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13150 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13150 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13150

/-! The local source numeric instances at 13150 have no network premises. -/
namespace BstLean.Part269.N13150
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13150)
open BstLean.Part268 (cell13150)

noncomputable def sourceNumerics13150 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13150 (cell13150 i)
      scalarRow13150.M scalarRow13150.H scalarRow13150.xi := by
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
    energy_allowance := scalarRow13150.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13150]
    centre_nonneg := (scalarRow13150.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13150])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13150
/-! Actual 13151 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13151
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13151 ≤ (1.035184490773 : ℝ) := by
  have hr : (114.677809536108 : ℝ) ≤ √(13151 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.677809536108 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13151 13151 (11 / 1000) ≤
    (0.008335412988 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13151) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.677809536108 : ℝ) ≤ √(13151 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13151)
  have hdiv : K / √(13151 : ℝ) ≤ K / 114.677809536108 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.677809536108 ≤ (0.008335412988 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13151.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13151 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13151 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13151 := gPlus_lower 13151
end BstLean.Part269.N13151

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13151
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035184490772 : ℝ) ≤ wn 13151 := by
  have hn : √(13151 : ℝ) ≤ 114.677809536109 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13151 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.677809536109 ≤ 2 / √(13151 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243096166 : ℝ) ≤ rhoBar 13151 BstLean.Part154.csC ∧
    rhoBar 13151 BstLean.Part154.csC ≤ 0.000243096543 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035184490772 : ℝ) / (1.295212 * 13151) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035184490773 : ℝ) / (1.29521 * 13151) := by gcongr
      _ ≤ (0.000243096543 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13151 BstLean.Part154.csC) ≤ 0.000972445268 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13151 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13151 BstLean.Part154.csC) (piBar (rhoBar 13151 BstLean.Part154.csC)) ≤ 0.000185678478 ∧
    cc1 (rhoBar 13151 BstLean.Part154.csC) (piBar (rhoBar 13151 BstLean.Part154.csC)) ≤ 0.000118148510 ∧
    cc2 (rhoBar 13151 BstLean.Part154.csC) ≤ 0.000068586191 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13151 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13151 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13151 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13151 BstLean.Part154.csC * nuR (rhoBar 13151 BstLean.Part154.csC)) ≤ 0.000486207860 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243096543 : ℝ) * 0.000972445268 := by gcongr
      _ ≤ (0.000486207860 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13151 BstLean.Part154.csC) * nuR (rhoBar 13151 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000972445268 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13151 BstLean.Part154.csC) * rhoBar 13151 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243096543 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243096543 / 2 + 0.399 * 0.000972445268 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185678478 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486207860 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118148510 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243096543 / 1.414213562 := by gcongr
      _ ≤ (0.000068586191 : ℝ) := by norm_num

end BstLean.Part269.N13151

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13151
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13151 BstLean.Part154.csC) (piBar (rhoBar 13151 BstLean.Part154.csC)) ≤ 1.48888E-7 := by
  have hr0 : 0 ≤ rhoBar 13151 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13151 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13151 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13151 BstLean.Part154.csC) (piBar (rhoBar 13151 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13151 BstLean.Part154.csC) (piBar (rhoBar 13151 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13151 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185678478 : ℝ) ^ 2 + 0.000118148510 ^ 2 + 3 * 0.000068586191 ^ 2 +
        2 * 0.797885 * 0.000185678478 * 0.000118148510 + 2 * 0.000185678478 * 0.000068586191 +
        4 * 0.797885 * 0.000118148510 * 0.000068586191 := by gcongr
    _ ≤ (1.48888E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13151 BstLean.Part154.csC Θ ≤ 0.002536058894 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13151 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13151 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13151 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13151 BstLean.Part154.csC) (piBar (rhoBar 13151 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13151 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035184490773 * 1.48888E-7 / (0.000243096166 : ℝ) := by gcongr
    _ ≤ 0.002536058894 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13151 BstLean.Part154.csC Θ ≤ 0.002812190215 + 0.000640821014 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13151 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13151 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13151 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035184490773 : ℝ) * ((2 * Θ * 0.000243096543 +
        (6863 / 10000) * 0.000243096543 * 13151 * 0.000972445268) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002812190215 + 0.000640821014 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13151 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13151 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13151 0.011 Θ ∧ gammaRatio 13151 0.011 Θ ≤ 0.000083570305 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13151 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035184490773 : ℝ) * 0.525 / ((1 - 0.011) * 13151) := by gcongr
      _ ≤ (0.000083570305 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13151 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13151 0.011 Θ) :=
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
    badAllowance 13151 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13151 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13151 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13151 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13151 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13151 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13151 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13151 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13151 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13151 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13151 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035184490773 : ℝ) * 13151 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13151 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003129075373 + 0.003176879908 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13151

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13151
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13151 BstLean.Part154.csC) (piBar (rhoBar 13151 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13151 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13151 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13151 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13151 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13151 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13151 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13151 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13151 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13151 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13151 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13151 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13151 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13151 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13151 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051566840751 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13151) ≤ 0.010413850648 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13151 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035184490773)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010413850648 + 2 * 0.737676 / 13151) := by gcongr
    _ ≤ (0.051566840751 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13151 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13151

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13151
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523264405 : ℝ) ≤ plow 13151 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13151) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052303537325)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331430920) : eMP 13151 0.011 xi bn ≤ 0.001146825985 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13151 : ℝ) * (1 - 0.011))) ≤ 0.000567096210 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001331430920 / (13151 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567096210 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567096210 : ℝ) + 3.141593 * 0.052303537325 / (13151 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001146825985 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052303537325)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331430920) : PiBarMP 13151 12 0.011 xi bn ≤ 0.158434591244 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13151 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036488778001 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.045337475935 : ℝ) ≤ √((13151 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.677809536108 : ℝ) ≤ √(13151 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13151) ≤ 0.121491754326 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036488778001 + 0.052303537325 * 1.772454 / (2 * (114.045337475935 : ℝ))) * (1 + 0.001146825985) +
        8 / (13151 * 114.677809536108) + 0.121491754326 := by gcongr
    _ ≤ (0.158434591244 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052303537325)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331430920) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280266506962) :
    parallelOracle 13151 0.011 xi bn cd ≤ 0.159390985360 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13151 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13151 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523264405 : ℝ) ≤ plow 13151 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.677809536108 : ℝ) ≤ √(13151 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280266506962 : ℝ) / (2 * 0.560523264405 * 114.677809536108)) * 0.158434591244 +
        0.280266506962 ^ 2 / (2 * 0.560523264405 * 114.677809536108) := by gcongr
    _ ≤ (0.159390985360 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052303537325) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331430920)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280266506962) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13151 13151 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523264405 : ℝ) ≤ plow 13151 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.677809536108 : ℝ) ≤ √(13151 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13151 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13151 Θ 1.22 ≤ 0.011563706225 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.677809536108 := by gcongr <;> linarith
      _ ≤ (0.011563706225 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13151 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13151 13151 0.011 ≤ 0.008335412988 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13151 13151 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13151 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13151 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13151 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13151 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159390985360 + 0.011563706225 + (0.008335412988 : ℝ) *
        (1 + 2 * (0.280266506962 + 0.011563706225) / (0.560523264405 * 114.677809536108))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13151]

end BstLean.Part269.N13151

/-! The original eight local profiles supply actual 13151 moment certificates. -/
namespace BstLean.Part269.N13151
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13151 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13151 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13151 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052303537325 ∧
    0 ≤ bN 13151 BstLean.Part154.csC (groupTheta g) ∧ bN 13151 BstLean.Part154.csC (groupTheta g) ≤ 0.001331430920 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13151 13151 0.011
      (momentAllowance 13151 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13151 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13151 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13151 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13151 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13151 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228699666211 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13151 0.011
      (momentAllowance 13151 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13151 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13151
/-! The actual computed-centre upper energy formula at 13151. -/
namespace BstLean.Part269.N13151
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13151

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13151
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13151)
open BstLean.Part268 (cell13151)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084273502157
  | 2 => 0.085197261845
  | 3 => 0.086116509967
  | 4 => 0.087032040318
  | 5 => 0.087944830669
  | 6 => 0.088856072221
  | 7 => 0.089767202260
  | 8 => 0.090679940103
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13151 13151 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13151 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13151

/-! Actual upper energy certificates on all 43 source endpoints at 13151. -/
namespace BstLean.Part269.N13151
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13151)
open BstLean.Part268 (cell13151)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13151 (gMinus 13151) (1 - (cell13151 i).lower) ≤ 1 ∧
    energyUpper 13151 (gMinus 13151) (BstLean.Part211.gPlus 13151)
      (finiteEnergy 13151 13151 0.011) (1 - (cell13151 i).lower) ≤
      (cell13151 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨10,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨11,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨12,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨13,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨14,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨15,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨16,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨17,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨18,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨19,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨20,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨21,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨22,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨23,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨24,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨25,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨26,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨27,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨28,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨29,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨30,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨31,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨32,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨33,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨34,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨35,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨36,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨37,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨38,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨39,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨40,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨41,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨42,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨43,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨44,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨45,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨46,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨47,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨48,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨49,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨50,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨51,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13151) (by norm_num)
        (q := 1 - (cell13151 ⟨52,by decide⟩).lower)
        (by norm_num [cell13151]) (by norm_num [cell13151])
      exact ⟨E.1,E.2.trans (by norm_num [cell13151])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13151

/-! Source-cell containment and simple scalar guards at 13151. -/
namespace BstLean.Part269.N13151
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13151)
open BstLean.Part268 (cell13151)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13151 ⟨10,by decide⟩).lower ∧ (cell13151 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13151 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13151 ⟨11,by decide⟩).lower ∧ (cell13151 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13151 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13151 ⟨12,by decide⟩).lower ∧ (cell13151 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13151 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13151 ⟨13,by decide⟩).lower ∧ (cell13151 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13151 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13151 ⟨14,by decide⟩).lower ∧ (cell13151 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13151 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13151 ⟨15,by decide⟩).lower ∧ (cell13151 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13151 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13151 ⟨16,by decide⟩).lower ∧ (cell13151 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13151 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13151 ⟨17,by decide⟩).lower ∧ (cell13151 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13151 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13151 ⟨18,by decide⟩).lower ∧ (cell13151 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13151 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13151 ⟨19,by decide⟩).lower ∧ (cell13151 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13151 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13151 ⟨20,by decide⟩).lower ∧ (cell13151 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13151 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13151 ⟨21,by decide⟩).lower ∧ (cell13151 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13151 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13151 ⟨22,by decide⟩).lower ∧ (cell13151 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13151 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13151 ⟨23,by decide⟩).lower ∧ (cell13151 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13151 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13151 ⟨24,by decide⟩).lower ∧ (cell13151 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13151 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13151 ⟨25,by decide⟩).lower ∧ (cell13151 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13151 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13151 ⟨26,by decide⟩).lower ∧ (cell13151 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13151 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13151 ⟨27,by decide⟩).lower ∧ (cell13151 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13151 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13151 ⟨28,by decide⟩).lower ∧ (cell13151 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13151 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13151 ⟨29,by decide⟩).lower ∧ (cell13151 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13151 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13151 ⟨30,by decide⟩).lower ∧ (cell13151 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13151 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13151 ⟨31,by decide⟩).lower ∧ (cell13151 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13151 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13151 ⟨32,by decide⟩).lower ∧ (cell13151 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13151 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13151 ⟨33,by decide⟩).lower ∧ (cell13151 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13151 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13151 ⟨34,by decide⟩).lower ∧ (cell13151 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13151 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13151 ⟨35,by decide⟩).lower ∧ (cell13151 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13151 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13151 ⟨36,by decide⟩).lower ∧ (cell13151 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13151 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13151 ⟨37,by decide⟩).lower ∧ (cell13151 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13151 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13151 ⟨38,by decide⟩).lower ∧ (cell13151 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13151 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13151 ⟨39,by decide⟩).lower ∧ (cell13151 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13151 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13151 ⟨40,by decide⟩).lower ∧ (cell13151 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13151 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13151 ⟨41,by decide⟩).lower ∧ (cell13151 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13151 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13151 ⟨42,by decide⟩).lower ∧ (cell13151 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13151 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13151 ⟨43,by decide⟩).lower ∧ (cell13151 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13151 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13151 ⟨44,by decide⟩).lower ∧ (cell13151 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13151 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13151 ⟨45,by decide⟩).lower ∧ (cell13151 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13151 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13151 ⟨46,by decide⟩).lower ∧ (cell13151 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13151 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13151 ⟨47,by decide⟩).lower ∧ (cell13151 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13151 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13151 ⟨48,by decide⟩).lower ∧ (cell13151 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13151 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13151 ⟨49,by decide⟩).lower ∧ (cell13151 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13151 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13151 ⟨50,by decide⟩).lower ∧ (cell13151 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13151 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13151 ⟨51,by decide⟩).lower ∧ (cell13151 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13151 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13151 ⟨52,by decide⟩).lower ∧ (cell13151 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13151 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13151 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13151 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13151,cell13151,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13151 i).lower ∧
    (cell13151 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13151 i).upper ≤ (0.532 : ℝ) ∧
    (cell13151 i).centre ≤ (0.1 : ℝ) ∧ (cell13151 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13151 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13151 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13151

/-! The local source numeric instances at 13151 have no network premises. -/
namespace BstLean.Part269.N13151
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13151)
open BstLean.Part268 (cell13151)

noncomputable def sourceNumerics13151 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13151 (cell13151 i)
      scalarRow13151.M scalarRow13151.H scalarRow13151.xi := by
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
    energy_allowance := scalarRow13151.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13151]
    centre_nonneg := (scalarRow13151.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13151])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13151
/-! Actual 13152 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13152
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13152 ≤ (1.035183141574 : ℝ) := by
  have hr : (114.682169494651 : ℝ) ≤ √(13152 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.682169494651 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13152 13152 (11 / 1000) ≤
    (0.008335096092 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13152) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.682169494651 : ℝ) ≤ √(13152 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13152)
  have hdiv : K / √(13152 : ℝ) ≤ K / 114.682169494651 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.682169494651 ≤ (0.008335096092 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13152.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13152 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13152 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13152 := gPlus_lower 13152
end BstLean.Part269.N13152

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13152
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035183141573 : ℝ) ≤ wn 13152 := by
  have hn : √(13152 : ℝ) ≤ 114.682169494652 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13152 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.682169494652 ≤ 2 / √(13152 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243077366 : ℝ) ≤ rhoBar 13152 BstLean.Part154.csC ∧
    rhoBar 13152 BstLean.Part154.csC ≤ 0.000243077742 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035183141573 : ℝ) / (1.295212 * 13152) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035183141574 : ℝ) / (1.29521 * 13152) := by gcongr
      _ ≤ (0.000243077742 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13152 BstLean.Part154.csC) ≤ 0.000972370055 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13152 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13152 BstLean.Part154.csC) (piBar (rhoBar 13152 BstLean.Part154.csC)) ≤ 0.000185664117 ∧
    cc1 (rhoBar 13152 BstLean.Part154.csC) (piBar (rhoBar 13152 BstLean.Part154.csC)) ≤ 0.000118139373 ∧
    cc2 (rhoBar 13152 BstLean.Part154.csC) ≤ 0.000068580886 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13152 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13152 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13152 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13152 BstLean.Part154.csC * nuR (rhoBar 13152 BstLean.Part154.csC)) ≤ 0.000486170256 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243077742 : ℝ) * 0.000972370055 := by gcongr
      _ ≤ (0.000486170256 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13152 BstLean.Part154.csC) * nuR (rhoBar 13152 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000972370055 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13152 BstLean.Part154.csC) * rhoBar 13152 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243077742 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243077742 / 2 + 0.399 * 0.000972370055 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185664117 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486170256 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118139373 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243077742 / 1.414213562 := by gcongr
      _ ≤ (0.000068580886 : ℝ) := by norm_num

end BstLean.Part269.N13152

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13152
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13152 BstLean.Part154.csC) (piBar (rhoBar 13152 BstLean.Part154.csC)) ≤ 1.48865E-7 := by
  have hr0 : 0 ≤ rhoBar 13152 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13152 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13152 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13152 BstLean.Part154.csC) (piBar (rhoBar 13152 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13152 BstLean.Part154.csC) (piBar (rhoBar 13152 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13152 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185664117 : ℝ) ^ 2 + 0.000118139373 ^ 2 + 3 * 0.000068580886 ^ 2 +
        2 * 0.797885 * 0.000185664117 * 0.000118139373 + 2 * 0.000185664117 * 0.000068580886 +
        4 * 0.797885 * 0.000118139373 * 0.000068580886 := by gcongr
    _ ≤ (1.48865E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13152 BstLean.Part154.csC Θ ≤ 0.002535859935 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13152 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13152 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13152 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13152 BstLean.Part154.csC) (piBar (rhoBar 13152 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13152 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035183141574 * 1.48865E-7 / (0.000243077366 : ℝ) := by gcongr
    _ ≤ 0.002535859935 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13152 BstLean.Part154.csC Θ ≤ 0.002811965372 + 0.000640770618 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13152 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13152 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13152 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035183141574 : ℝ) * ((2 * Θ * 0.000243077742 +
        (6863 / 10000) * 0.000243077742 * 13152 * 0.000972370055) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002811965372 + 0.000640770618 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13152 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13152 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13152 0.011 Θ ∧ gammaRatio 13152 0.011 Θ ≤ 0.000083563842 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13152 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035183141574 : ℝ) * 0.525 / ((1 - 0.011) * 13152) := by gcongr
      _ ≤ (0.000083563842 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13152 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13152 0.011 Θ) :=
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
    badAllowance 13152 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13152 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13152 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13152 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13152 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13152 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13152 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13152 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13152 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13152 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13152 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035183141574 : ℝ) * 13152 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13152 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003128850530 + 0.003176630553 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13152

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13152
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13152 BstLean.Part154.csC) (piBar (rhoBar 13152 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13152 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13152 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13152 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13152 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13152 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13152 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13152 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13152 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13152 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13152 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13152 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13152 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13152 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13152 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051564859398 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13152) ≤ 0.010413454736 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13152 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035183141574)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010413454736 + 2 * 0.737676 / 13152) := by gcongr
    _ ≤ (0.051564859398 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13152 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13152

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13152
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523306576 : ℝ) ≤ plow 13152 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13152) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052303181571)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331326466) : eMP 13152 0.011 xi bn ≤ 0.001146737331 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13152 : ℝ) * (1 - 0.011))) ≤ 0.000567052406 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001331326466 / (13152 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567052406 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567052406 : ℝ) + 3.141593 * 0.052303181571 / (13152 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001146737331 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052303181571)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331326466) : PiBarMP 13152 12 0.011 xi bn ≤ 0.158428517301 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13152 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036487346657 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.049673388396 : ℝ) ≤ √((13152 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.682169494651 : ℝ) ≤ √(13152 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13152) ≤ 0.121487135482 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036487346657 + 0.052303181571 * 1.772454 / (2 * (114.049673388396 : ℝ))) * (1 + 0.001146737331) +
        8 / (13152 * 114.682169494651) + 0.121487135482 := by gcongr
    _ ≤ (0.158428517301 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052303181571)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331326466) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280263747833) :
    parallelOracle 13152 0.011 xi bn cd ≤ 0.159384846314 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13152 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13152 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523306576 : ℝ) ≤ plow 13152 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.682169494651 : ℝ) ≤ √(13152 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280263747833 : ℝ) / (2 * 0.560523306576 * 114.682169494651)) * 0.158428517301 +
        0.280263747833 ^ 2 / (2 * 0.560523306576 * 114.682169494651) := by gcongr
    _ ≤ (0.159384846314 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052303181571) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331326466)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280263747833) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13152 13152 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523306576 : ℝ) ≤ plow 13152 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.682169494651 : ℝ) ≤ √(13152 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13152 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13152 Θ 1.22 ≤ 0.011563266599 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.682169494651 := by gcongr <;> linarith
      _ ≤ (0.011563266599 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13152 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13152 13152 0.011 ≤ 0.008335096092 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13152 13152 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13152 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13152 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13152 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13152 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159384846314 + 0.011563266599 + (0.008335096092 : ℝ) *
        (1 + 2 * (0.280263747833 + 0.011563266599) / (0.560523306576 * 114.682169494651))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13152]

end BstLean.Part269.N13152

/-! The original eight local profiles supply actual 13152 moment certificates. -/
namespace BstLean.Part269.N13152
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13152 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13152 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13152 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052303181571 ∧
    0 ≤ bN 13152 BstLean.Part154.csC (groupTheta g) ∧ bN 13152 BstLean.Part154.csC (groupTheta g) ≤ 0.001331326466 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13152 13152 0.011
      (momentAllowance 13152 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13152 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13152 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13152 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13152 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13152 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228698888435 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13152 0.011
      (momentAllowance 13152 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13152 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13152
/-! The actual computed-centre upper energy formula at 13152. -/
namespace BstLean.Part269.N13152
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13152

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13152
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13152)
open BstLean.Part268 (cell13152)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084270997847
  | 2 => 0.085194726900
  | 3 => 0.086113940075
  | 4 => 0.087029430135
  | 5 => 0.087942173625
  | 6 => 0.088853360301
  | 7 => 0.089764425759
  | 8 => 0.090677087345
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13152 13152 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13152 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13152

/-! Actual upper energy certificates on all 43 source endpoints at 13152. -/
namespace BstLean.Part269.N13152
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13152)
open BstLean.Part268 (cell13152)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13152 (gMinus 13152) (1 - (cell13152 i).lower) ≤ 1 ∧
    energyUpper 13152 (gMinus 13152) (BstLean.Part211.gPlus 13152)
      (finiteEnergy 13152 13152 0.011) (1 - (cell13152 i).lower) ≤
      (cell13152 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨10,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨11,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨12,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨13,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨14,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨15,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨16,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨17,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨18,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨19,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨20,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨21,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨22,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨23,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨24,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨25,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨26,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨27,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨28,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨29,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨30,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨31,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨32,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨33,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨34,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨35,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨36,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨37,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨38,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨39,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨40,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨41,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨42,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨43,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨44,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨45,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨46,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨47,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨48,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨49,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨50,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨51,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13152) (by norm_num)
        (q := 1 - (cell13152 ⟨52,by decide⟩).lower)
        (by norm_num [cell13152]) (by norm_num [cell13152])
      exact ⟨E.1,E.2.trans (by norm_num [cell13152])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13152

/-! Source-cell containment and simple scalar guards at 13152. -/
namespace BstLean.Part269.N13152
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13152)
open BstLean.Part268 (cell13152)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13152 ⟨10,by decide⟩).lower ∧ (cell13152 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13152 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13152 ⟨11,by decide⟩).lower ∧ (cell13152 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13152 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13152 ⟨12,by decide⟩).lower ∧ (cell13152 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13152 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13152 ⟨13,by decide⟩).lower ∧ (cell13152 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13152 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13152 ⟨14,by decide⟩).lower ∧ (cell13152 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13152 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13152 ⟨15,by decide⟩).lower ∧ (cell13152 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13152 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13152 ⟨16,by decide⟩).lower ∧ (cell13152 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13152 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13152 ⟨17,by decide⟩).lower ∧ (cell13152 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13152 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13152 ⟨18,by decide⟩).lower ∧ (cell13152 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13152 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13152 ⟨19,by decide⟩).lower ∧ (cell13152 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13152 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13152 ⟨20,by decide⟩).lower ∧ (cell13152 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13152 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13152 ⟨21,by decide⟩).lower ∧ (cell13152 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13152 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13152 ⟨22,by decide⟩).lower ∧ (cell13152 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13152 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13152 ⟨23,by decide⟩).lower ∧ (cell13152 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13152 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13152 ⟨24,by decide⟩).lower ∧ (cell13152 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13152 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13152 ⟨25,by decide⟩).lower ∧ (cell13152 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13152 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13152 ⟨26,by decide⟩).lower ∧ (cell13152 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13152 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13152 ⟨27,by decide⟩).lower ∧ (cell13152 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13152 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13152 ⟨28,by decide⟩).lower ∧ (cell13152 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13152 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13152 ⟨29,by decide⟩).lower ∧ (cell13152 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13152 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13152 ⟨30,by decide⟩).lower ∧ (cell13152 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13152 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13152 ⟨31,by decide⟩).lower ∧ (cell13152 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13152 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13152 ⟨32,by decide⟩).lower ∧ (cell13152 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13152 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13152 ⟨33,by decide⟩).lower ∧ (cell13152 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13152 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13152 ⟨34,by decide⟩).lower ∧ (cell13152 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13152 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13152 ⟨35,by decide⟩).lower ∧ (cell13152 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13152 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13152 ⟨36,by decide⟩).lower ∧ (cell13152 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13152 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13152 ⟨37,by decide⟩).lower ∧ (cell13152 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13152 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13152 ⟨38,by decide⟩).lower ∧ (cell13152 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13152 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13152 ⟨39,by decide⟩).lower ∧ (cell13152 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13152 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13152 ⟨40,by decide⟩).lower ∧ (cell13152 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13152 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13152 ⟨41,by decide⟩).lower ∧ (cell13152 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13152 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13152 ⟨42,by decide⟩).lower ∧ (cell13152 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13152 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13152 ⟨43,by decide⟩).lower ∧ (cell13152 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13152 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13152 ⟨44,by decide⟩).lower ∧ (cell13152 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13152 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13152 ⟨45,by decide⟩).lower ∧ (cell13152 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13152 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13152 ⟨46,by decide⟩).lower ∧ (cell13152 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13152 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13152 ⟨47,by decide⟩).lower ∧ (cell13152 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13152 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13152 ⟨48,by decide⟩).lower ∧ (cell13152 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13152 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13152 ⟨49,by decide⟩).lower ∧ (cell13152 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13152 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13152 ⟨50,by decide⟩).lower ∧ (cell13152 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13152 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13152 ⟨51,by decide⟩).lower ∧ (cell13152 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13152 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13152 ⟨52,by decide⟩).lower ∧ (cell13152 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13152 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13152 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13152 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13152,cell13152,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13152 i).lower ∧
    (cell13152 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13152 i).upper ≤ (0.532 : ℝ) ∧
    (cell13152 i).centre ≤ (0.1 : ℝ) ∧ (cell13152 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13152 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13152 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13152

/-! The local source numeric instances at 13152 have no network premises. -/
namespace BstLean.Part269.N13152
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13152)
open BstLean.Part268 (cell13152)

noncomputable def sourceNumerics13152 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13152 (cell13152 i)
      scalarRow13152.M scalarRow13152.H scalarRow13152.xi := by
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
    energy_allowance := scalarRow13152.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13152]
    centre_nonneg := (scalarRow13152.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13152])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13152
/-! Actual 13153 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13153
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13153 ≤ (1.035181792531 : ℝ) := by
  have hr : (114.686529287445 : ℝ) ≤ √(13153 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.686529287445 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13153 13153 (11 / 1000) ≤
    (0.008334779233 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13153) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.686529287445 : ℝ) ≤ √(13153 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13153)
  have hdiv : K / √(13153 : ℝ) ≤ K / 114.686529287445 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.686529287445 ≤ (0.008334779233 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13153.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13153 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13153 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13153 := gPlus_lower 13153
end BstLean.Part269.N13153

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13153
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035181792530 : ℝ) ≤ wn 13153 := by
  have hn : √(13153 : ℝ) ≤ 114.686529287446 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13153 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.686529287446 ≤ 2 / √(13153 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243058568 : ℝ) ≤ rhoBar 13153 BstLean.Part154.csC ∧
    rhoBar 13153 BstLean.Part154.csC ≤ 0.000243058945 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035181792530 : ℝ) / (1.295212 * 13153) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035181792531 : ℝ) / (1.29521 * 13153) := by gcongr
      _ ≤ (0.000243058945 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13153 BstLean.Part154.csC) ≤ 0.000972294858 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13153 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13153 BstLean.Part154.csC) (piBar (rhoBar 13153 BstLean.Part154.csC)) ≤ 0.000185649759 ∧
    cc1 (rhoBar 13153 BstLean.Part154.csC) (piBar (rhoBar 13153 BstLean.Part154.csC)) ≤ 0.000118130237 ∧
    cc2 (rhoBar 13153 BstLean.Part154.csC) ≤ 0.000068575583 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13153 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13153 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13153 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13153 BstLean.Part154.csC * nuR (rhoBar 13153 BstLean.Part154.csC)) ≤ 0.000486132660 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243058945 : ℝ) * 0.000972294858 := by gcongr
      _ ≤ (0.000486132660 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13153 BstLean.Part154.csC) * nuR (rhoBar 13153 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000972294858 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13153 BstLean.Part154.csC) * rhoBar 13153 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243058945 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243058945 / 2 + 0.399 * 0.000972294858 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185649759 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486132660 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118130237 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243058945 / 1.414213562 := by gcongr
      _ ≤ (0.000068575583 : ℝ) := by norm_num

end BstLean.Part269.N13153

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13153
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13153 BstLean.Part154.csC) (piBar (rhoBar 13153 BstLean.Part154.csC)) ≤ 1.48842E-7 := by
  have hr0 : 0 ≤ rhoBar 13153 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13153 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13153 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13153 BstLean.Part154.csC) (piBar (rhoBar 13153 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13153 BstLean.Part154.csC) (piBar (rhoBar 13153 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13153 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185649759 : ℝ) ^ 2 + 0.000118130237 ^ 2 + 3 * 0.000068575583 ^ 2 +
        2 * 0.797885 * 0.000185649759 * 0.000118130237 + 2 * 0.000185649759 * 0.000068575583 +
        4 * 0.797885 * 0.000118130237 * 0.000068575583 := by gcongr
    _ ≤ (1.48842E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13153 BstLean.Part154.csC Θ ≤ 0.002535660926 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13153 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13153 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13153 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13153 BstLean.Part154.csC) (piBar (rhoBar 13153 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13153 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035181792531 * 1.48842E-7 / (0.000243058568 : ℝ) := by gcongr
    _ ≤ 0.002535660926 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13153 BstLean.Part154.csC Θ ≤ 0.002811740590 + 0.000640720232 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13153 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13153 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13153 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035181792531 : ℝ) * ((2 * Θ * 0.000243058945 +
        (6863 / 10000) * 0.000243058945 * 13153 * 0.000972294858) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002811740590 + 0.000640720232 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13153 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13153 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13153 0.011 Θ ∧ gammaRatio 13153 0.011 Θ ≤ 0.000083557380 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13153 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035181792531 : ℝ) * 0.525 / ((1 - 0.011) * 13153) := by gcongr
      _ ≤ (0.000083557380 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13153 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13153 0.011 Θ) :=
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
    badAllowance 13153 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13153 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13153 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13153 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13153 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13153 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13153 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13153 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13153 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13153 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13153 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035181792531 : ℝ) * 13153 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13153 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003128625748 + 0.003176381158 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13153

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13153
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13153 BstLean.Part154.csC) (piBar (rhoBar 13153 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13153 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13153 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13153 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13153 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13153 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13153 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13153 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13153 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13153 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13153 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13153 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13153 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13153 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13153 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051562878277 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13153) ≤ 0.010413058870 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13153 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035181792531)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010413058870 + 2 * 0.737676 / 13153) := by gcongr
    _ ≤ (0.051562878277 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13153 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13153

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13153
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523348741 : ℝ) ≤ plow 13153 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13153) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052302825856)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331221987) : eMP 13153 0.011 xi bn ≤ 0.001146648672 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13153 : ℝ) * (1 - 0.011))) ≤ 0.000567008600 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001331221987 / (13153 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000567008600 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000567008600 : ℝ) + 3.141593 * 0.052302825856 / (13153 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001146648672 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052302825856)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331221987) : PiBarMP 13153 12 0.011 xi bn ≤ 0.158422443487 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13153 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036485914913 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.054009136022 : ℝ) ≤ √((13153 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.686529287445 : ℝ) ≤ √(13153 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13153) ≤ 0.121482517165 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036485914913 + 0.052302825856 * 1.772454 / (2 * (114.054009136022 : ℝ))) * (1 + 0.001146648672) +
        8 / (13153 * 114.686529287445) + 0.121482517165 := by gcongr
    _ ≤ (0.158422443487 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052302825856)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331221987) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280260989017) :
    parallelOracle 13153 0.011 xi bn cd ≤ 0.159378707406 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13153 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13153 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523348741 : ℝ) ≤ plow 13153 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.686529287445 : ℝ) ≤ √(13153 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280260989017 : ℝ) / (2 * 0.560523348741 * 114.686529287445)) * 0.158422443487 +
        0.280260989017 ^ 2 / (2 * 0.560523348741 * 114.686529287445) := by gcongr
    _ ≤ (0.159378707406 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052302825856) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331221987)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280260989017) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13153 13153 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523348741 : ℝ) ≤ plow 13153 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.686529287445 : ℝ) ≤ √(13153 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13153 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13153 Θ 1.22 ≤ 0.011562827023 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.686529287445 := by gcongr <;> linarith
      _ ≤ (0.011562827023 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13153 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13153 13153 0.011 ≤ 0.008334779233 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13153 13153 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13153 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13153 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13153 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13153 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159378707406 + 0.011562827023 + (0.008334779233 : ℝ) *
        (1 + 2 * (0.280260989017 + 0.011562827023) / (0.560523348741 * 114.686529287445))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13153]

end BstLean.Part269.N13153

/-! The original eight local profiles supply actual 13153 moment certificates. -/
namespace BstLean.Part269.N13153
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13153 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13153 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13153 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052302825856 ∧
    0 ≤ bN 13153 BstLean.Part154.csC (groupTheta g) ∧ bN 13153 BstLean.Part154.csC (groupTheta g) ≤ 0.001331221987 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13153 13153 0.011
      (momentAllowance 13153 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13153 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13153 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13153 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13153 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13153 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228698110740 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13153 0.011
      (momentAllowance 13153 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13153 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13153
/-! The actual computed-centre upper energy formula at 13153. -/
namespace BstLean.Part269.N13153
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13153

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13153
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13153)
open BstLean.Part268 (cell13153)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084268494240
  | 2 => 0.085192192683
  | 3 => 0.086111370940
  | 4 => 0.087026820746
  | 5 => 0.087939517418
  | 6 => 0.088850649272
  | 7 => 0.089761650214
  | 8 => 0.090674235625
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13153 13153 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13153 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13153

/-! Actual upper energy certificates on all 43 source endpoints at 13153. -/
namespace BstLean.Part269.N13153
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13153)
open BstLean.Part268 (cell13153)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13153 (gMinus 13153) (1 - (cell13153 i).lower) ≤ 1 ∧
    energyUpper 13153 (gMinus 13153) (BstLean.Part211.gPlus 13153)
      (finiteEnergy 13153 13153 0.011) (1 - (cell13153 i).lower) ≤
      (cell13153 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨10,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨11,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨12,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨13,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨14,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨15,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨16,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨17,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨18,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨19,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨20,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨21,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨22,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨23,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨24,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨25,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨26,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨27,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨28,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨29,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨30,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨31,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨32,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨33,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨34,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨35,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨36,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨37,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨38,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨39,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨40,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨41,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨42,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨43,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨44,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨45,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨46,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨47,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨48,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨49,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨50,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨51,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13153) (by norm_num)
        (q := 1 - (cell13153 ⟨52,by decide⟩).lower)
        (by norm_num [cell13153]) (by norm_num [cell13153])
      exact ⟨E.1,E.2.trans (by norm_num [cell13153])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13153

/-! Source-cell containment and simple scalar guards at 13153. -/
namespace BstLean.Part269.N13153
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13153)
open BstLean.Part268 (cell13153)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13153 ⟨10,by decide⟩).lower ∧ (cell13153 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13153 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13153 ⟨11,by decide⟩).lower ∧ (cell13153 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13153 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13153 ⟨12,by decide⟩).lower ∧ (cell13153 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13153 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13153 ⟨13,by decide⟩).lower ∧ (cell13153 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13153 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13153 ⟨14,by decide⟩).lower ∧ (cell13153 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13153 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13153 ⟨15,by decide⟩).lower ∧ (cell13153 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13153 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13153 ⟨16,by decide⟩).lower ∧ (cell13153 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13153 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13153 ⟨17,by decide⟩).lower ∧ (cell13153 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13153 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13153 ⟨18,by decide⟩).lower ∧ (cell13153 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13153 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13153 ⟨19,by decide⟩).lower ∧ (cell13153 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13153 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13153 ⟨20,by decide⟩).lower ∧ (cell13153 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13153 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13153 ⟨21,by decide⟩).lower ∧ (cell13153 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13153 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13153 ⟨22,by decide⟩).lower ∧ (cell13153 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13153 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13153 ⟨23,by decide⟩).lower ∧ (cell13153 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13153 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13153 ⟨24,by decide⟩).lower ∧ (cell13153 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13153 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13153 ⟨25,by decide⟩).lower ∧ (cell13153 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13153 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13153 ⟨26,by decide⟩).lower ∧ (cell13153 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13153 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13153 ⟨27,by decide⟩).lower ∧ (cell13153 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13153 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13153 ⟨28,by decide⟩).lower ∧ (cell13153 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13153 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13153 ⟨29,by decide⟩).lower ∧ (cell13153 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13153 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13153 ⟨30,by decide⟩).lower ∧ (cell13153 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13153 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13153 ⟨31,by decide⟩).lower ∧ (cell13153 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13153 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13153 ⟨32,by decide⟩).lower ∧ (cell13153 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13153 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13153 ⟨33,by decide⟩).lower ∧ (cell13153 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13153 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13153 ⟨34,by decide⟩).lower ∧ (cell13153 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13153 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13153 ⟨35,by decide⟩).lower ∧ (cell13153 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13153 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13153 ⟨36,by decide⟩).lower ∧ (cell13153 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13153 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13153 ⟨37,by decide⟩).lower ∧ (cell13153 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13153 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13153 ⟨38,by decide⟩).lower ∧ (cell13153 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13153 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13153 ⟨39,by decide⟩).lower ∧ (cell13153 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13153 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13153 ⟨40,by decide⟩).lower ∧ (cell13153 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13153 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13153 ⟨41,by decide⟩).lower ∧ (cell13153 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13153 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13153 ⟨42,by decide⟩).lower ∧ (cell13153 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13153 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13153 ⟨43,by decide⟩).lower ∧ (cell13153 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13153 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13153 ⟨44,by decide⟩).lower ∧ (cell13153 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13153 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13153 ⟨45,by decide⟩).lower ∧ (cell13153 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13153 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13153 ⟨46,by decide⟩).lower ∧ (cell13153 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13153 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13153 ⟨47,by decide⟩).lower ∧ (cell13153 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13153 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13153 ⟨48,by decide⟩).lower ∧ (cell13153 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13153 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13153 ⟨49,by decide⟩).lower ∧ (cell13153 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13153 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13153 ⟨50,by decide⟩).lower ∧ (cell13153 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13153 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13153 ⟨51,by decide⟩).lower ∧ (cell13153 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13153 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13153 ⟨52,by decide⟩).lower ∧ (cell13153 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13153 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13153 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13153 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13153,cell13153,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13153 i).lower ∧
    (cell13153 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13153 i).upper ≤ (0.532 : ℝ) ∧
    (cell13153 i).centre ≤ (0.1 : ℝ) ∧ (cell13153 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13153 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13153 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13153

/-! The local source numeric instances at 13153 have no network premises. -/
namespace BstLean.Part269.N13153
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13153)
open BstLean.Part268 (cell13153)

noncomputable def sourceNumerics13153 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13153 (cell13153 i)
      scalarRow13153.M scalarRow13153.H scalarRow13153.xi := by
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
    energy_allowance := scalarRow13153.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13153]
    centre_nonneg := (scalarRow13153.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13153])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13153
/-! Actual 13154 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13154
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13154 ≤ (1.035180443642 : ℝ) := by
  have hr : (114.690888914507 : ℝ) ≤ √(13154 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.690888914507 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13154 13154 (11 / 1000) ≤
    (0.008334462409 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13154) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.690888914507 : ℝ) ≤ √(13154 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13154)
  have hdiv : K / √(13154 : ℝ) ≤ K / 114.690888914507 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.690888914507 ≤ (0.008334462409 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13154.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13154 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13154 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13154 := gPlus_lower 13154
end BstLean.Part269.N13154

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13154
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035180443641 : ℝ) ≤ wn 13154 := by
  have hn : √(13154 : ℝ) ≤ 114.690888914508 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13154 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.690888914508 ≤ 2 / √(13154 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243039774 : ℝ) ≤ rhoBar 13154 BstLean.Part154.csC ∧
    rhoBar 13154 BstLean.Part154.csC ≤ 0.000243040150 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035180443641 : ℝ) / (1.295212 * 13154) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035180443642 : ℝ) / (1.29521 * 13154) := by gcongr
      _ ≤ (0.000243040150 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13154 BstLean.Part154.csC) ≤ 0.000972219669 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13154 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13154 BstLean.Part154.csC) (piBar (rhoBar 13154 BstLean.Part154.csC)) ≤ 0.000185635403 ∧
    cc1 (rhoBar 13154 BstLean.Part154.csC) (piBar (rhoBar 13154 BstLean.Part154.csC)) ≤ 0.000118121102 ∧
    cc2 (rhoBar 13154 BstLean.Part154.csC) ≤ 0.000068570280 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13154 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13154 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13154 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13154 BstLean.Part154.csC * nuR (rhoBar 13154 BstLean.Part154.csC)) ≤ 0.000486095068 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243040150 : ℝ) * 0.000972219669 := by gcongr
      _ ≤ (0.000486095068 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13154 BstLean.Part154.csC) * nuR (rhoBar 13154 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000972219669 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13154 BstLean.Part154.csC) * rhoBar 13154 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243040150 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243040150 / 2 + 0.399 * 0.000972219669 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185635403 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486095068 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118121102 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243040150 / 1.414213562 := by gcongr
      _ ≤ (0.000068570280 : ℝ) := by norm_num

end BstLean.Part269.N13154

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13154
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13154 BstLean.Part154.csC) (piBar (rhoBar 13154 BstLean.Part154.csC)) ≤ 1.48819E-7 := by
  have hr0 : 0 ≤ rhoBar 13154 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13154 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13154 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13154 BstLean.Part154.csC) (piBar (rhoBar 13154 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13154 BstLean.Part154.csC) (piBar (rhoBar 13154 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13154 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185635403 : ℝ) ^ 2 + 0.000118121102 ^ 2 + 3 * 0.000068570280 ^ 2 +
        2 * 0.797885 * 0.000185635403 * 0.000118121102 + 2 * 0.000185635403 * 0.000068570280 +
        4 * 0.797885 * 0.000118121102 * 0.000068570280 := by gcongr
    _ ≤ (1.48819E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13154 BstLean.Part154.csC Θ ≤ 0.002535461845 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13154 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13154 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13154 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13154 BstLean.Part154.csC) (piBar (rhoBar 13154 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13154 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035180443642 * 1.48819E-7 / (0.000243039774 : ℝ) := by gcongr
    _ ≤ 0.002535461845 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13154 BstLean.Part154.csC Θ ≤ 0.002811515822 + 0.000640669853 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13154 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13154 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13154 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035180443642 : ℝ) * ((2 * Θ * 0.000243040150 +
        (6863 / 10000) * 0.000243040150 * 13154 * 0.000972219669) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002811515822 + 0.000640669853 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13154 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13154 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13154 0.011 Θ ∧ gammaRatio 13154 0.011 Θ ≤ 0.000083550919 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13154 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035180443642 : ℝ) * 0.525 / ((1 - 0.011) * 13154) := by gcongr
      _ ≤ (0.000083550919 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13154 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13154 0.011 Θ) :=
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
    badAllowance 13154 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13154 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13154 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13154 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13154 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13154 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13154 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13154 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13154 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13154 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13154 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035180443642 : ℝ) * 13154 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13154 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003128400980 + 0.003176131698 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13154

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13154
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13154 BstLean.Part154.csC) (piBar (rhoBar 13154 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13154 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13154 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13154 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13154 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13154 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13154 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13154 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13154 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13154 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13154 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13154 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13154 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13154 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13154 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051560897383 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13154) ≤ 0.010412663049 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13154 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035180443642)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010412663049 + 2 * 0.737676 / 13154) := by gcongr
    _ ≤ (0.051560897383 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13154 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13154

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13154
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523390900 : ℝ) ≤ plow 13154 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13154) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052302470122)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331117469) : eMP 13154 0.011 xi bn ≤ 0.001146560002 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13154 : ℝ) * (1 - 0.011))) ≤ 0.000566964788 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001331117469 / (13154 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566964788 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566964788 : ℝ) + 3.141593 * 0.052302470122 / (13154 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001146560002 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052302470122)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331117469) : PiBarMP 13154 12 0.011 xi bn ≤ 0.158416369612 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13154 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036484482579 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.058344718832 : ℝ) ≤ √((13154 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.690888914507 : ℝ) ≤ √(13154 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13154) ≤ 0.121477899375 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036484482579 + 0.052302470122 * 1.772454 / (2 * (114.058344718832 : ℝ))) * (1 + 0.001146560002) +
        8 / (13154 * 114.690888914507) + 0.121477899375 := by gcongr
    _ ≤ (0.158416369612 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052302470122)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331117469) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280258230385) :
    parallelOracle 13154 0.011 xi bn cd ≤ 0.159372568445 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13154 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13154 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523390900 : ℝ) ≤ plow 13154 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.690888914507 : ℝ) ≤ √(13154 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280258230385 : ℝ) / (2 * 0.560523390900 * 114.690888914507)) * 0.158416369612 +
        0.280258230385 ^ 2 / (2 * 0.560523390900 * 114.690888914507) := by gcongr
    _ ≤ (0.159372568445 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052302470122) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331117469)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280258230385) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13154 13154 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523390900 : ℝ) ≤ plow 13154 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.690888914507 : ℝ) ≤ √(13154 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13154 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13154 Θ 1.22 ≤ 0.011562387497 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.690888914507 := by gcongr <;> linarith
      _ ≤ (0.011562387497 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13154 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13154 13154 0.011 ≤ 0.008334462409 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13154 13154 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13154 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13154 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13154 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13154 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159372568445 + 0.011562387497 + (0.008334462409 : ℝ) *
        (1 + 2 * (0.280258230385 + 0.011562387497) / (0.560523390900 * 114.690888914507))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13154]

end BstLean.Part269.N13154

/-! The original eight local profiles supply actual 13154 moment certificates. -/
namespace BstLean.Part269.N13154
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13154 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13154 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13154 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052302470122 ∧
    0 ≤ bN 13154 BstLean.Part154.csC (groupTheta g) ∧ bN 13154 BstLean.Part154.csC (groupTheta g) ≤ 0.001331117469 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13154 13154 0.011
      (momentAllowance 13154 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13154 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13154 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13154 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13154 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13154 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228697333002 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13154 0.011
      (momentAllowance 13154 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13154 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13154
/-! The actual computed-centre upper energy formula at 13154. -/
namespace BstLean.Part269.N13154
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13154

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13154
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13154)
open BstLean.Part268 (cell13154)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084265991338
  | 2 => 0.085189659193
  | 3 => 0.086108802562
  | 4 => 0.087024212148
  | 5 => 0.087936862047
  | 6 => 0.088847939134
  | 7 => 0.089758875626
  | 8 => 0.090671384940
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13154 13154 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13154 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13154

/-! Actual upper energy certificates on all 43 source endpoints at 13154. -/
namespace BstLean.Part269.N13154
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13154)
open BstLean.Part268 (cell13154)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13154 (gMinus 13154) (1 - (cell13154 i).lower) ≤ 1 ∧
    energyUpper 13154 (gMinus 13154) (BstLean.Part211.gPlus 13154)
      (finiteEnergy 13154 13154 0.011) (1 - (cell13154 i).lower) ≤
      (cell13154 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨10,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨11,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨12,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨13,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨14,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨15,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨16,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨17,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨18,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨19,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨20,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨21,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨22,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨23,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨24,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨25,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨26,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨27,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨28,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨29,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨30,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨31,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨32,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨33,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨34,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨35,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨36,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨37,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨38,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨39,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨40,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨41,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨42,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨43,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨44,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨45,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨46,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨47,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨48,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨49,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨50,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨51,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13154) (by norm_num)
        (q := 1 - (cell13154 ⟨52,by decide⟩).lower)
        (by norm_num [cell13154]) (by norm_num [cell13154])
      exact ⟨E.1,E.2.trans (by norm_num [cell13154])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13154

/-! Source-cell containment and simple scalar guards at 13154. -/
namespace BstLean.Part269.N13154
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13154)
open BstLean.Part268 (cell13154)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13154 ⟨10,by decide⟩).lower ∧ (cell13154 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13154 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13154 ⟨11,by decide⟩).lower ∧ (cell13154 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13154 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13154 ⟨12,by decide⟩).lower ∧ (cell13154 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13154 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13154 ⟨13,by decide⟩).lower ∧ (cell13154 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13154 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13154 ⟨14,by decide⟩).lower ∧ (cell13154 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13154 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13154 ⟨15,by decide⟩).lower ∧ (cell13154 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13154 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13154 ⟨16,by decide⟩).lower ∧ (cell13154 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13154 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13154 ⟨17,by decide⟩).lower ∧ (cell13154 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13154 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13154 ⟨18,by decide⟩).lower ∧ (cell13154 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13154 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13154 ⟨19,by decide⟩).lower ∧ (cell13154 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13154 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13154 ⟨20,by decide⟩).lower ∧ (cell13154 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13154 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13154 ⟨21,by decide⟩).lower ∧ (cell13154 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13154 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13154 ⟨22,by decide⟩).lower ∧ (cell13154 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13154 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13154 ⟨23,by decide⟩).lower ∧ (cell13154 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13154 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13154 ⟨24,by decide⟩).lower ∧ (cell13154 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13154 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13154 ⟨25,by decide⟩).lower ∧ (cell13154 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13154 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13154 ⟨26,by decide⟩).lower ∧ (cell13154 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13154 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13154 ⟨27,by decide⟩).lower ∧ (cell13154 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13154 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13154 ⟨28,by decide⟩).lower ∧ (cell13154 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13154 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13154 ⟨29,by decide⟩).lower ∧ (cell13154 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13154 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13154 ⟨30,by decide⟩).lower ∧ (cell13154 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13154 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13154 ⟨31,by decide⟩).lower ∧ (cell13154 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13154 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13154 ⟨32,by decide⟩).lower ∧ (cell13154 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13154 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13154 ⟨33,by decide⟩).lower ∧ (cell13154 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13154 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13154 ⟨34,by decide⟩).lower ∧ (cell13154 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13154 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13154 ⟨35,by decide⟩).lower ∧ (cell13154 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13154 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13154 ⟨36,by decide⟩).lower ∧ (cell13154 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13154 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13154 ⟨37,by decide⟩).lower ∧ (cell13154 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13154 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13154 ⟨38,by decide⟩).lower ∧ (cell13154 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13154 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13154 ⟨39,by decide⟩).lower ∧ (cell13154 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13154 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13154 ⟨40,by decide⟩).lower ∧ (cell13154 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13154 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13154 ⟨41,by decide⟩).lower ∧ (cell13154 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13154 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13154 ⟨42,by decide⟩).lower ∧ (cell13154 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13154 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13154 ⟨43,by decide⟩).lower ∧ (cell13154 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13154 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13154 ⟨44,by decide⟩).lower ∧ (cell13154 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13154 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13154 ⟨45,by decide⟩).lower ∧ (cell13154 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13154 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13154 ⟨46,by decide⟩).lower ∧ (cell13154 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13154 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13154 ⟨47,by decide⟩).lower ∧ (cell13154 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13154 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13154 ⟨48,by decide⟩).lower ∧ (cell13154 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13154 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13154 ⟨49,by decide⟩).lower ∧ (cell13154 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13154 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13154 ⟨50,by decide⟩).lower ∧ (cell13154 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13154 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13154 ⟨51,by decide⟩).lower ∧ (cell13154 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13154 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13154 ⟨52,by decide⟩).lower ∧ (cell13154 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13154 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13154 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13154 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13154,cell13154,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13154 i).lower ∧
    (cell13154 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13154 i).upper ≤ (0.532 : ℝ) ∧
    (cell13154 i).centre ≤ (0.1 : ℝ) ∧ (cell13154 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13154 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13154 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13154

/-! The local source numeric instances at 13154 have no network premises. -/
namespace BstLean.Part269.N13154
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13154)
open BstLean.Part268 (cell13154)

noncomputable def sourceNumerics13154 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13154 (cell13154 i)
      scalarRow13154.M scalarRow13154.H scalarRow13154.xi := by
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
    energy_allowance := scalarRow13154.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13154]
    centre_nonneg := (scalarRow13154.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13154])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13154
/-! Actual 13155 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13155
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13155 ≤ (1.035179094908 : ℝ) := by
  have hr : (114.695248375859 : ℝ) ≤ √(13155 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.695248375859 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13155 13155 (11 / 1000) ≤
    (0.008334145621 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13155) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.695248375859 : ℝ) ≤ √(13155 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13155)
  have hdiv : K / √(13155 : ℝ) ≤ K / 114.695248375859 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.695248375859 ≤ (0.008334145621 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13155.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13155 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13155 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13155 := gPlus_lower 13155
end BstLean.Part269.N13155

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13155
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035179094907 : ℝ) ≤ wn 13155 := by
  have hn : √(13155 : ℝ) ≤ 114.695248375860 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13155 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.695248375860 ≤ 2 / √(13155 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243020982 : ℝ) ≤ rhoBar 13155 BstLean.Part154.csC ∧
    rhoBar 13155 BstLean.Part154.csC ≤ 0.000243021358 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035179094907 : ℝ) / (1.295212 * 13155) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035179094908 : ℝ) / (1.29521 * 13155) := by gcongr
      _ ≤ (0.000243021358 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13155 BstLean.Part154.csC) ≤ 0.000972144492 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13155 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13155 BstLean.Part154.csC) (piBar (rhoBar 13155 BstLean.Part154.csC)) ≤ 0.000185621049 ∧
    cc1 (rhoBar 13155 BstLean.Part154.csC) (piBar (rhoBar 13155 BstLean.Part154.csC)) ≤ 0.000118111968 ∧
    cc2 (rhoBar 13155 BstLean.Part154.csC) ≤ 0.000068564979 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13155 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13155 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13155 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13155 BstLean.Part154.csC * nuR (rhoBar 13155 BstLean.Part154.csC)) ≤ 0.000486057481 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243021358 : ℝ) * 0.000972144492 := by gcongr
      _ ≤ (0.000486057481 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13155 BstLean.Part154.csC) * nuR (rhoBar 13155 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000972144492 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13155 BstLean.Part154.csC) * rhoBar 13155 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243021358 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243021358 / 2 + 0.399 * 0.000972144492 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185621049 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486057481 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118111968 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243021358 / 1.414213562 := by gcongr
      _ ≤ (0.000068564979 : ℝ) := by norm_num

end BstLean.Part269.N13155

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13155
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13155 BstLean.Part154.csC) (piBar (rhoBar 13155 BstLean.Part154.csC)) ≤ 1.48796E-7 := by
  have hr0 : 0 ≤ rhoBar 13155 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13155 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13155 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13155 BstLean.Part154.csC) (piBar (rhoBar 13155 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13155 BstLean.Part154.csC) (piBar (rhoBar 13155 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13155 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185621049 : ℝ) ^ 2 + 0.000118111968 ^ 2 + 3 * 0.000068564979 ^ 2 +
        2 * 0.797885 * 0.000185621049 * 0.000118111968 + 2 * 0.000185621049 * 0.000068564979 +
        4 * 0.797885 * 0.000118111968 * 0.000068564979 := by gcongr
    _ ≤ (1.48796E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13155 BstLean.Part154.csC Θ ≤ 0.002535262715 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13155 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13155 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13155 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13155 BstLean.Part154.csC) (piBar (rhoBar 13155 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13155 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035179094908 * 1.48796E-7 / (0.000243020982 : ℝ) := by gcongr
    _ ≤ 0.002535262715 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13155 BstLean.Part154.csC Θ ≤ 0.002811291093 + 0.000640619481 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13155 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13155 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13155 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035179094908 : ℝ) * ((2 * Θ * 0.000243021358 +
        (6863 / 10000) * 0.000243021358 * 13155 * 0.000972144492) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002811291093 + 0.000640619481 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13155 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13155 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13155 0.011 Θ ∧ gammaRatio 13155 0.011 Θ ≤ 0.000083544459 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13155 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035179094908 : ℝ) * 0.525 / ((1 - 0.011) * 13155) := by gcongr
      _ ≤ (0.000083544459 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13155 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13155 0.011 Θ) :=
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
    badAllowance 13155 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13155 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13155 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13155 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13155 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13155 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13155 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13155 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13155 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13155 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13155 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035179094908 : ℝ) * 13155 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13155 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003128176251 + 0.003175882196 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13155

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13155
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13155 BstLean.Part154.csC) (piBar (rhoBar 13155 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13155 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13155 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13155 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13155 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13155 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13155 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13155 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13155 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13155 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13155 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13155 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13155 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13155 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13155 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051558916720 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13155) ≤ 0.010412267274 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13155 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035179094908)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010412267274 + 2 * 0.737676 / 13155) := by gcongr
    _ ≤ (0.051558916720 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13155 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13155

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13155
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523433052 : ℝ) ≤ plow 13155 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13155) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052302114404)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331012926) : eMP 13155 0.011 xi bn ≤ 0.001146471330 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13155 : ℝ) * (1 - 0.011))) ≤ 0.000566920975 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001331012926 / (13155 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566920975 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566920975 : ℝ) + 3.141593 * 0.052302114404 / (13155 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001146471330 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052302114404)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331012926) : PiBarMP 13155 12 0.011 xi bn ≤ 0.158410295866 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13155 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036483049846 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.062680136844 : ℝ) ≤ √((13155 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.695248375859 : ℝ) ≤ √(13155 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13155) ≤ 0.121473282112 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036483049846 + 0.052302114404 * 1.772454 / (2 * (114.062680136844 : ℝ))) * (1 + 0.001146471330) +
        8 / (13155 * 114.695248375859) + 0.121473282112 := by gcongr
    _ ≤ (0.158410295866 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052302114404)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331012926) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280255472016) :
    parallelOracle 13155 0.011 xi bn cd ≤ 0.159366429621 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13155 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13155 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523433052 : ℝ) ≤ plow 13155 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.695248375859 : ℝ) ≤ √(13155 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280255472016 : ℝ) / (2 * 0.560523433052 * 114.695248375859)) * 0.158410295866 +
        0.280255472016 ^ 2 / (2 * 0.560523433052 * 114.695248375859) := by gcongr
    _ ≤ (0.159366429621 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052302114404) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001331012926)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280255472016) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13155 13155 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523433052 : ℝ) ≤ plow 13155 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.695248375859 : ℝ) ≤ √(13155 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13155 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13155 Θ 1.22 ≤ 0.011561948022 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.695248375859 := by gcongr <;> linarith
      _ ≤ (0.011561948022 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13155 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13155 13155 0.011 ≤ 0.008334145621 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13155 13155 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13155 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13155 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13155 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13155 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159366429621 + 0.011561948022 + (0.008334145621 : ℝ) *
        (1 + 2 * (0.280255472016 + 0.011561948022) / (0.560523433052 * 114.695248375859))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13155]

end BstLean.Part269.N13155

/-! The original eight local profiles supply actual 13155 moment certificates. -/
namespace BstLean.Part269.N13155
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13155 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13155 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13155 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052302114404 ∧
    0 ≤ bN 13155 BstLean.Part154.csC (groupTheta g) ∧ bN 13155 BstLean.Part154.csC (groupTheta g) ≤ 0.001331012926 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13155 13155 0.011
      (momentAllowance 13155 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13155 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13155 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13155 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13155 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13155 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228696555296 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13155 0.011
      (momentAllowance 13155 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13155 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13155
/-! The actual computed-centre upper energy formula at 13155. -/
namespace BstLean.Part269.N13155
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13155

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13155
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13155)
open BstLean.Part268 (cell13155)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084263489139
  | 2 => 0.085187126429
  | 3 => 0.086106234939
  | 4 => 0.087021604342
  | 5 => 0.087934207513
  | 6 => 0.088845229886
  | 7 => 0.089756101993
  | 8 => 0.090668535291
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13155 13155 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13155 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13155

/-! Actual upper energy certificates on all 43 source endpoints at 13155. -/
namespace BstLean.Part269.N13155
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13155)
open BstLean.Part268 (cell13155)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13155 (gMinus 13155) (1 - (cell13155 i).lower) ≤ 1 ∧
    energyUpper 13155 (gMinus 13155) (BstLean.Part211.gPlus 13155)
      (finiteEnergy 13155 13155 0.011) (1 - (cell13155 i).lower) ≤
      (cell13155 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨10,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨11,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨12,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨13,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨14,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨15,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨16,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨17,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨18,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨19,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨20,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨21,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨22,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨23,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨24,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨25,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨26,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨27,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨28,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨29,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨30,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨31,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨32,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨33,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨34,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨35,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨36,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨37,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨38,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨39,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨40,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨41,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨42,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨43,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨44,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨45,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨46,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨47,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨48,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨49,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨50,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨51,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13155) (by norm_num)
        (q := 1 - (cell13155 ⟨52,by decide⟩).lower)
        (by norm_num [cell13155]) (by norm_num [cell13155])
      exact ⟨E.1,E.2.trans (by norm_num [cell13155])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13155

/-! Source-cell containment and simple scalar guards at 13155. -/
namespace BstLean.Part269.N13155
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13155)
open BstLean.Part268 (cell13155)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13155 ⟨10,by decide⟩).lower ∧ (cell13155 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13155 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13155 ⟨11,by decide⟩).lower ∧ (cell13155 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13155 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13155 ⟨12,by decide⟩).lower ∧ (cell13155 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13155 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13155 ⟨13,by decide⟩).lower ∧ (cell13155 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13155 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13155 ⟨14,by decide⟩).lower ∧ (cell13155 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13155 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13155 ⟨15,by decide⟩).lower ∧ (cell13155 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13155 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13155 ⟨16,by decide⟩).lower ∧ (cell13155 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13155 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13155 ⟨17,by decide⟩).lower ∧ (cell13155 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13155 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13155 ⟨18,by decide⟩).lower ∧ (cell13155 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13155 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13155 ⟨19,by decide⟩).lower ∧ (cell13155 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13155 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13155 ⟨20,by decide⟩).lower ∧ (cell13155 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13155 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13155 ⟨21,by decide⟩).lower ∧ (cell13155 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13155 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13155 ⟨22,by decide⟩).lower ∧ (cell13155 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13155 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13155 ⟨23,by decide⟩).lower ∧ (cell13155 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13155 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13155 ⟨24,by decide⟩).lower ∧ (cell13155 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13155 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13155 ⟨25,by decide⟩).lower ∧ (cell13155 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13155 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13155 ⟨26,by decide⟩).lower ∧ (cell13155 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13155 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13155 ⟨27,by decide⟩).lower ∧ (cell13155 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13155 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13155 ⟨28,by decide⟩).lower ∧ (cell13155 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13155 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13155 ⟨29,by decide⟩).lower ∧ (cell13155 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13155 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13155 ⟨30,by decide⟩).lower ∧ (cell13155 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13155 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13155 ⟨31,by decide⟩).lower ∧ (cell13155 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13155 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13155 ⟨32,by decide⟩).lower ∧ (cell13155 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13155 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13155 ⟨33,by decide⟩).lower ∧ (cell13155 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13155 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13155 ⟨34,by decide⟩).lower ∧ (cell13155 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13155 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13155 ⟨35,by decide⟩).lower ∧ (cell13155 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13155 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13155 ⟨36,by decide⟩).lower ∧ (cell13155 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13155 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13155 ⟨37,by decide⟩).lower ∧ (cell13155 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13155 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13155 ⟨38,by decide⟩).lower ∧ (cell13155 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13155 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13155 ⟨39,by decide⟩).lower ∧ (cell13155 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13155 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13155 ⟨40,by decide⟩).lower ∧ (cell13155 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13155 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13155 ⟨41,by decide⟩).lower ∧ (cell13155 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13155 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13155 ⟨42,by decide⟩).lower ∧ (cell13155 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13155 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13155 ⟨43,by decide⟩).lower ∧ (cell13155 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13155 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13155 ⟨44,by decide⟩).lower ∧ (cell13155 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13155 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13155 ⟨45,by decide⟩).lower ∧ (cell13155 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13155 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13155 ⟨46,by decide⟩).lower ∧ (cell13155 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13155 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13155 ⟨47,by decide⟩).lower ∧ (cell13155 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13155 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13155 ⟨48,by decide⟩).lower ∧ (cell13155 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13155 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13155 ⟨49,by decide⟩).lower ∧ (cell13155 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13155 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13155 ⟨50,by decide⟩).lower ∧ (cell13155 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13155 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13155 ⟨51,by decide⟩).lower ∧ (cell13155 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13155 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13155 ⟨52,by decide⟩).lower ∧ (cell13155 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13155 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13155 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13155 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13155,cell13155,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13155 i).lower ∧
    (cell13155 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13155 i).upper ≤ (0.532 : ℝ) ∧
    (cell13155 i).centre ≤ (0.1 : ℝ) ∧ (cell13155 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13155 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13155 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13155

/-! The local source numeric instances at 13155 have no network premises. -/
namespace BstLean.Part269.N13155
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13155)
open BstLean.Part268 (cell13155)

noncomputable def sourceNumerics13155 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13155 (cell13155 i)
      scalarRow13155.M scalarRow13155.H scalarRow13155.xi := by
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
    energy_allowance := scalarRow13155.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13155]
    centre_nonneg := (scalarRow13155.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13155])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13155
/-! Actual 13156 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13156
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13156 ≤ (1.035177746328 : ℝ) := by
  have hr : (114.699607671517 : ℝ) ≤ √(13156 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.699607671517 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13156 13156 (11 / 1000) ≤
    (0.008333828870 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13156) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.699607671517 : ℝ) ≤ √(13156 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13156)
  have hdiv : K / √(13156 : ℝ) ≤ K / 114.699607671517 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.699607671517 ≤ (0.008333828870 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13156.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13156 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13156 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13156 := gPlus_lower 13156
end BstLean.Part269.N13156

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13156
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035177746327 : ℝ) ≤ wn 13156 := by
  have hn : √(13156 : ℝ) ≤ 114.699607671518 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13156 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.699607671518 ≤ 2 / √(13156 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000243002193 : ℝ) ≤ rhoBar 13156 BstLean.Part154.csC ∧
    rhoBar 13156 BstLean.Part154.csC ≤ 0.000243002569 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035177746327 : ℝ) / (1.295212 * 13156) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035177746328 : ℝ) / (1.29521 * 13156) := by gcongr
      _ ≤ (0.000243002569 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13156 BstLean.Part154.csC) ≤ 0.000972069327 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13156 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13156 BstLean.Part154.csC) (piBar (rhoBar 13156 BstLean.Part154.csC)) ≤ 0.000185606697 ∧
    cc1 (rhoBar 13156 BstLean.Part154.csC) (piBar (rhoBar 13156 BstLean.Part154.csC)) ≤ 0.000118102836 ∧
    cc2 (rhoBar 13156 BstLean.Part154.csC) ≤ 0.000068559678 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13156 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13156 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13156 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13156 BstLean.Part154.csC * nuR (rhoBar 13156 BstLean.Part154.csC)) ≤ 0.000486019901 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000243002569 : ℝ) * 0.000972069327 := by gcongr
      _ ≤ (0.000486019901 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13156 BstLean.Part154.csC) * nuR (rhoBar 13156 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000972069327 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13156 BstLean.Part154.csC) * rhoBar 13156 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000243002569 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000243002569 / 2 + 0.399 * 0.000972069327 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185606697 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000486019901 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118102836 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000243002569 / 1.414213562 := by gcongr
      _ ≤ (0.000068559678 : ℝ) := by norm_num

end BstLean.Part269.N13156

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13156
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13156 BstLean.Part154.csC) (piBar (rhoBar 13156 BstLean.Part154.csC)) ≤ 1.48773E-7 := by
  have hr0 : 0 ≤ rhoBar 13156 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13156 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13156 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13156 BstLean.Part154.csC) (piBar (rhoBar 13156 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13156 BstLean.Part154.csC) (piBar (rhoBar 13156 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13156 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185606697 : ℝ) ^ 2 + 0.000118102836 ^ 2 + 3 * 0.000068559678 ^ 2 +
        2 * 0.797885 * 0.000185606697 * 0.000118102836 + 2 * 0.000185606697 * 0.000068559678 +
        4 * 0.797885 * 0.000118102836 * 0.000068559678 := by gcongr
    _ ≤ (1.48773E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13156 BstLean.Part154.csC Θ ≤ 0.002535063523 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13156 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13156 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13156 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13156 BstLean.Part154.csC) (piBar (rhoBar 13156 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13156 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035177746328 * 1.48773E-7 / (0.000243002193 : ℝ) := by gcongr
    _ ≤ 0.002535063523 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13156 BstLean.Part154.csC Θ ≤ 0.002811066401 + 0.000640569118 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13156 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13156 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13156 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035177746328 : ℝ) * ((2 * Θ * 0.000243002569 +
        (6863 / 10000) * 0.000243002569 * 13156 * 0.000972069327) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002811066401 + 0.000640569118 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13156 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13156 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13156 0.011 Θ ∧ gammaRatio 13156 0.011 Θ ≤ 0.000083538000 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13156 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035177746328 : ℝ) * 0.525 / ((1 - 0.011) * 13156) := by gcongr
      _ ≤ (0.000083538000 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13156 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13156 0.011 Θ) :=
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
    badAllowance 13156 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13156 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13156 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13156 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13156 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13156 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13156 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13156 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13156 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13156 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13156 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035177746328 : ℝ) * 13156 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13156 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003127951559 + 0.003175632641 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13156

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13156
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13156 BstLean.Part154.csC) (piBar (rhoBar 13156 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13156 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13156 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13156 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13156 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13156 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13156 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13156 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13156 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13156 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13156 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13156 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13156 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13156 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13156 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051556936279 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13156) ≤ 0.010411871543 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13156 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035177746328)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010411871543 + 2 * 0.737676 / 13156) := by gcongr
    _ ≤ (0.051556936279 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13156 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13156

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13156
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523475197 : ℝ) ≤ plow 13156 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13156) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052301758696)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330908350) : eMP 13156 0.011 xi bn ≤ 0.001146382650 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13156 : ℝ) * (1 - 0.011))) ≤ 0.000566877158 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001330908350 / (13156 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566877158 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566877158 : ℝ) + 3.141593 * 0.052301758696 / (13156 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001146382650 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052301758696)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330908350) : PiBarMP 13156 12 0.011 xi bn ≤ 0.158404222139 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13156 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036481616604 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.067015390076 : ℝ) ≤ √((13156 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.699607671517 : ℝ) ≤ √(13156 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13156) ≤ 0.121468665374 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036481616604 + 0.052301758696 * 1.772454 / (2 * (114.067015390076 : ℝ))) * (1 + 0.001146382650) +
        8 / (13156 * 114.699607671517) + 0.121468665374 := by gcongr
    _ ≤ (0.158404222139 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052301758696)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330908350) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280252713888) :
    parallelOracle 13156 0.011 xi bn cd ≤ 0.159360290825 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13156 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13156 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523475197 : ℝ) ≤ plow 13156 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.699607671517 : ℝ) ≤ √(13156 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280252713888 : ℝ) / (2 * 0.560523475197 * 114.699607671517)) * 0.158404222139 +
        0.280252713888 ^ 2 / (2 * 0.560523475197 * 114.699607671517) := by gcongr
    _ ≤ (0.159360290825 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052301758696) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330908350)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280252713888) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13156 13156 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523475197 : ℝ) ≤ plow 13156 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.699607671517 : ℝ) ≤ √(13156 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13156 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13156 Θ 1.22 ≤ 0.011561508596 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.699607671517 := by gcongr <;> linarith
      _ ≤ (0.011561508596 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13156 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13156 13156 0.011 ≤ 0.008333828870 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13156 13156 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13156 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13156 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13156 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13156 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159360290825 + 0.011561508596 + (0.008333828870 : ℝ) *
        (1 + 2 * (0.280252713888 + 0.011561508596) / (0.560523475197 * 114.699607671517))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13156]

end BstLean.Part269.N13156

/-! The original eight local profiles supply actual 13156 moment certificates. -/
namespace BstLean.Part269.N13156
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13156 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13156 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13156 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052301758696 ∧
    0 ≤ bN 13156 BstLean.Part154.csC (groupTheta g) ∧ bN 13156 BstLean.Part154.csC (groupTheta g) ≤ 0.001330908350 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13156 13156 0.011
      (momentAllowance 13156 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13156 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13156 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13156 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13156 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13156 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228695777609 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13156 0.011
      (momentAllowance 13156 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13156 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13156
/-! The actual computed-centre upper energy formula at 13156. -/
namespace BstLean.Part269.N13156
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13156

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13156
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13156)
open BstLean.Part268 (cell13156)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084260987642
  | 2 => 0.085184594391
  | 3 => 0.086103668071
  | 4 => 0.087018997327
  | 5 => 0.087931553813
  | 6 => 0.088842521526
  | 7 => 0.089753329315
  | 8 => 0.090665686675
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13156 13156 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13156 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13156

/-! Actual upper energy certificates on all 43 source endpoints at 13156. -/
namespace BstLean.Part269.N13156
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13156)
open BstLean.Part268 (cell13156)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13156 (gMinus 13156) (1 - (cell13156 i).lower) ≤ 1 ∧
    energyUpper 13156 (gMinus 13156) (BstLean.Part211.gPlus 13156)
      (finiteEnergy 13156 13156 0.011) (1 - (cell13156 i).lower) ≤
      (cell13156 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨10,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨11,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨12,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨13,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨14,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨15,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨16,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨17,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨18,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨19,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨20,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨21,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨22,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨23,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨24,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨25,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨26,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨27,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨28,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨29,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨30,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨31,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨32,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨33,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨34,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨35,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨36,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨37,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨38,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨39,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨40,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨41,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨42,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨43,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨44,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨45,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨46,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨47,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨48,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨49,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨50,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨51,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13156) (by norm_num)
        (q := 1 - (cell13156 ⟨52,by decide⟩).lower)
        (by norm_num [cell13156]) (by norm_num [cell13156])
      exact ⟨E.1,E.2.trans (by norm_num [cell13156])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13156

/-! Source-cell containment and simple scalar guards at 13156. -/
namespace BstLean.Part269.N13156
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13156)
open BstLean.Part268 (cell13156)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13156 ⟨10,by decide⟩).lower ∧ (cell13156 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13156 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13156 ⟨11,by decide⟩).lower ∧ (cell13156 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13156 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13156 ⟨12,by decide⟩).lower ∧ (cell13156 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13156 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13156 ⟨13,by decide⟩).lower ∧ (cell13156 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13156 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13156 ⟨14,by decide⟩).lower ∧ (cell13156 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13156 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13156 ⟨15,by decide⟩).lower ∧ (cell13156 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13156 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13156 ⟨16,by decide⟩).lower ∧ (cell13156 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13156 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13156 ⟨17,by decide⟩).lower ∧ (cell13156 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13156 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13156 ⟨18,by decide⟩).lower ∧ (cell13156 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13156 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13156 ⟨19,by decide⟩).lower ∧ (cell13156 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13156 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13156 ⟨20,by decide⟩).lower ∧ (cell13156 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13156 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13156 ⟨21,by decide⟩).lower ∧ (cell13156 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13156 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13156 ⟨22,by decide⟩).lower ∧ (cell13156 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13156 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13156 ⟨23,by decide⟩).lower ∧ (cell13156 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13156 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13156 ⟨24,by decide⟩).lower ∧ (cell13156 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13156 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13156 ⟨25,by decide⟩).lower ∧ (cell13156 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13156 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13156 ⟨26,by decide⟩).lower ∧ (cell13156 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13156 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13156 ⟨27,by decide⟩).lower ∧ (cell13156 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13156 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13156 ⟨28,by decide⟩).lower ∧ (cell13156 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13156 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13156 ⟨29,by decide⟩).lower ∧ (cell13156 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13156 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13156 ⟨30,by decide⟩).lower ∧ (cell13156 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13156 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13156 ⟨31,by decide⟩).lower ∧ (cell13156 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13156 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13156 ⟨32,by decide⟩).lower ∧ (cell13156 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13156 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13156 ⟨33,by decide⟩).lower ∧ (cell13156 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13156 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13156 ⟨34,by decide⟩).lower ∧ (cell13156 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13156 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13156 ⟨35,by decide⟩).lower ∧ (cell13156 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13156 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13156 ⟨36,by decide⟩).lower ∧ (cell13156 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13156 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13156 ⟨37,by decide⟩).lower ∧ (cell13156 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13156 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13156 ⟨38,by decide⟩).lower ∧ (cell13156 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13156 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13156 ⟨39,by decide⟩).lower ∧ (cell13156 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13156 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13156 ⟨40,by decide⟩).lower ∧ (cell13156 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13156 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13156 ⟨41,by decide⟩).lower ∧ (cell13156 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13156 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13156 ⟨42,by decide⟩).lower ∧ (cell13156 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13156 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13156 ⟨43,by decide⟩).lower ∧ (cell13156 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13156 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13156 ⟨44,by decide⟩).lower ∧ (cell13156 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13156 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13156 ⟨45,by decide⟩).lower ∧ (cell13156 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13156 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13156 ⟨46,by decide⟩).lower ∧ (cell13156 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13156 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13156 ⟨47,by decide⟩).lower ∧ (cell13156 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13156 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13156 ⟨48,by decide⟩).lower ∧ (cell13156 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13156 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13156 ⟨49,by decide⟩).lower ∧ (cell13156 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13156 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13156 ⟨50,by decide⟩).lower ∧ (cell13156 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13156 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13156 ⟨51,by decide⟩).lower ∧ (cell13156 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13156 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13156 ⟨52,by decide⟩).lower ∧ (cell13156 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13156 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13156 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13156 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13156,cell13156,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13156 i).lower ∧
    (cell13156 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13156 i).upper ≤ (0.532 : ℝ) ∧
    (cell13156 i).centre ≤ (0.1 : ℝ) ∧ (cell13156 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13156 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13156 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13156

/-! The local source numeric instances at 13156 have no network premises. -/
namespace BstLean.Part269.N13156
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13156)
open BstLean.Part268 (cell13156)

noncomputable def sourceNumerics13156 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13156 (cell13156 i)
      scalarRow13156.M scalarRow13156.H scalarRow13156.xi := by
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
    energy_allowance := scalarRow13156.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13156]
    centre_nonneg := (scalarRow13156.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13156])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13156
/-! Actual 13157 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13157
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13157 ≤ (1.035176397903 : ℝ) := by
  have hr : (114.703966801501 : ℝ) ≤ √(13157 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.703966801501 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13157 13157 (11 / 1000) ≤
    (0.008333512154 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13157) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.703966801501 : ℝ) ≤ √(13157 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13157)
  have hdiv : K / √(13157 : ℝ) ≤ K / 114.703966801501 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.703966801501 ≤ (0.008333512154 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13157.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13157 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13157 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13157 := gPlus_lower 13157
end BstLean.Part269.N13157

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13157
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035176397902 : ℝ) ≤ wn 13157 := by
  have hn : √(13157 : ℝ) ≤ 114.703966801502 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13157 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.703966801502 ≤ 2 / √(13157 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242983407 : ℝ) ≤ rhoBar 13157 BstLean.Part154.csC ∧
    rhoBar 13157 BstLean.Part154.csC ≤ 0.000242983784 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035176397902 : ℝ) / (1.295212 * 13157) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035176397903 : ℝ) / (1.29521 * 13157) := by gcongr
      _ ≤ (0.000242983784 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13157 BstLean.Part154.csC) ≤ 0.000971994178 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13157 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13157 BstLean.Part154.csC) (piBar (rhoBar 13157 BstLean.Part154.csC)) ≤ 0.000185592349 ∧
    cc1 (rhoBar 13157 BstLean.Part154.csC) (piBar (rhoBar 13157 BstLean.Part154.csC)) ≤ 0.000118093706 ∧
    cc2 (rhoBar 13157 BstLean.Part154.csC) ≤ 0.000068554378 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13157 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13157 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13157 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13157 BstLean.Part154.csC * nuR (rhoBar 13157 BstLean.Part154.csC)) ≤ 0.000485982329 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242983784 : ℝ) * 0.000971994178 := by gcongr
      _ ≤ (0.000485982329 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13157 BstLean.Part154.csC) * nuR (rhoBar 13157 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000971994178 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13157 BstLean.Part154.csC) * rhoBar 13157 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242983784 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242983784 / 2 + 0.399 * 0.000971994178 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185592349 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485982329 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118093706 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242983784 / 1.414213562 := by gcongr
      _ ≤ (0.000068554378 : ℝ) := by norm_num

end BstLean.Part269.N13157

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13157
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13157 BstLean.Part154.csC) (piBar (rhoBar 13157 BstLean.Part154.csC)) ≤ 1.48750E-7 := by
  have hr0 : 0 ≤ rhoBar 13157 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13157 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13157 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13157 BstLean.Part154.csC) (piBar (rhoBar 13157 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13157 BstLean.Part154.csC) (piBar (rhoBar 13157 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13157 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185592349 : ℝ) ^ 2 + 0.000118093706 ^ 2 + 3 * 0.000068554378 ^ 2 +
        2 * 0.797885 * 0.000185592349 * 0.000118093706 + 2 * 0.000185592349 * 0.000068554378 +
        4 * 0.797885 * 0.000118093706 * 0.000068554378 := by gcongr
    _ ≤ (1.48750E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13157 BstLean.Part154.csC Θ ≤ 0.002534864271 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13157 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13157 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13157 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13157 BstLean.Part154.csC) (piBar (rhoBar 13157 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13157 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035176397903 * 1.48750E-7 / (0.000242983407 : ℝ) := by gcongr
    _ ≤ 0.002534864271 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13157 BstLean.Part154.csC Θ ≤ 0.002810841771 + 0.000640518765 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13157 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13157 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13157 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035176397903 : ℝ) * ((2 * Θ * 0.000242983784 +
        (6863 / 10000) * 0.000242983784 * 13157 * 0.000971994178) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002810841771 + 0.000640518765 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13157 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13157 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13157 0.011 Θ ∧ gammaRatio 13157 0.011 Θ ≤ 0.000083531542 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13157 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035176397903 : ℝ) * 0.525 / ((1 - 0.011) * 13157) := by gcongr
      _ ≤ (0.000083531542 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13157 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13157 0.011 Θ) :=
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
    badAllowance 13157 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13157 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13157 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13157 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13157 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13157 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13157 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13157 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13157 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13157 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13157 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035176397903 : ℝ) * 13157 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13157 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003127726929 + 0.003175383036 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13157

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13157
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13157 BstLean.Part154.csC) (piBar (rhoBar 13157 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13157 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13157 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13157 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13157 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13157 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13157 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13157 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13157 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13157 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13157 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13157 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13157 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13157 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13157 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051554956065 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13157) ≤ 0.010411475857 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13157 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035176397903)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010411475857 + 2 * 0.737676 / 13157) := by gcongr
    _ ≤ (0.051554956065 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13157 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13157

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13157
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523517336 : ℝ) ≤ plow 13157 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13157) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052301403023)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330803743) : eMP 13157 0.011 xi bn ≤ 0.001146293963 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13157 : ℝ) * (1 - 0.011))) ≤ 0.000566833337 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001330803743 / (13157 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566833337 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566833337 : ℝ) + 3.141593 * 0.052301403023 / (13157 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001146293963 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052301403023)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330803743) : PiBarMP 13157 12 0.011 xi bn ≤ 0.158398148458 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13157 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036480182881 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.071350478549 : ℝ) ≤ √((13157 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.703966801501 : ℝ) ≤ √(13157 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13157) ≤ 0.121464049163 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036480182881 + 0.052301403023 * 1.772454 / (2 * (114.071350478549 : ℝ))) * (1 + 0.001146293963) +
        8 / (13157 * 114.703966801501) + 0.121464049163 := by gcongr
    _ ≤ (0.158398148458 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052301403023)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330803743) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280249956061) :
    parallelOracle 13157 0.011 xi bn cd ≤ 0.159354152083 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13157 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13157 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523517336 : ℝ) ≤ plow 13157 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.703966801501 : ℝ) ≤ √(13157 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280249956061 : ℝ) / (2 * 0.560523517336 * 114.703966801501)) * 0.158398148458 +
        0.280249956061 ^ 2 / (2 * 0.560523517336 * 114.703966801501) := by gcongr
    _ ≤ (0.159354152083 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052301403023) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330803743)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280249956061) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13157 13157 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523517336 : ℝ) ≤ plow 13157 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.703966801501 : ℝ) ≤ √(13157 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13157 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13157 Θ 1.22 ≤ 0.011561069220 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.703966801501 := by gcongr <;> linarith
      _ ≤ (0.011561069220 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13157 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13157 13157 0.011 ≤ 0.008333512154 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13157 13157 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13157 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13157 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13157 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13157 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159354152083 + 0.011561069220 + (0.008333512154 : ℝ) *
        (1 + 2 * (0.280249956061 + 0.011561069220) / (0.560523517336 * 114.703966801501))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13157]

end BstLean.Part269.N13157

/-! The original eight local profiles supply actual 13157 moment certificates. -/
namespace BstLean.Part269.N13157
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13157 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13157 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13157 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052301403023 ∧
    0 ≤ bN 13157 BstLean.Part154.csC (groupTheta g) ∧ bN 13157 BstLean.Part154.csC (groupTheta g) ≤ 0.001330803743 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13157 13157 0.011
      (momentAllowance 13157 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13157 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13157 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13157 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13157 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13157 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228694999996 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13157 0.011
      (momentAllowance 13157 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13157 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13157
/-! The actual computed-centre upper energy formula at 13157. -/
namespace BstLean.Part269.N13157
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13157

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13157
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13157)
open BstLean.Part268 (cell13157)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084258486847
  | 2 => 0.085182063079
  | 3 => 0.086101101958
  | 4 => 0.087016391102
  | 5 => 0.087928900947
  | 6 => 0.088839814055
  | 7 => 0.089750557590
  | 8 => 0.090662839092
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13157 13157 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13157 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13157

/-! Actual upper energy certificates on all 43 source endpoints at 13157. -/
namespace BstLean.Part269.N13157
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13157)
open BstLean.Part268 (cell13157)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13157 (gMinus 13157) (1 - (cell13157 i).lower) ≤ 1 ∧
    energyUpper 13157 (gMinus 13157) (BstLean.Part211.gPlus 13157)
      (finiteEnergy 13157 13157 0.011) (1 - (cell13157 i).lower) ≤
      (cell13157 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨10,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨11,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨12,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨13,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨14,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨15,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨16,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨17,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨18,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨19,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨20,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨21,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨22,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨23,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨24,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨25,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨26,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨27,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨28,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨29,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨30,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨31,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨32,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨33,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨34,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨35,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨36,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨37,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨38,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨39,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨40,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨41,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨42,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨43,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨44,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨45,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨46,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨47,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨48,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨49,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨50,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨51,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13157) (by norm_num)
        (q := 1 - (cell13157 ⟨52,by decide⟩).lower)
        (by norm_num [cell13157]) (by norm_num [cell13157])
      exact ⟨E.1,E.2.trans (by norm_num [cell13157])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13157

/-! Source-cell containment and simple scalar guards at 13157. -/
namespace BstLean.Part269.N13157
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13157)
open BstLean.Part268 (cell13157)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13157 ⟨10,by decide⟩).lower ∧ (cell13157 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13157 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13157 ⟨11,by decide⟩).lower ∧ (cell13157 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13157 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13157 ⟨12,by decide⟩).lower ∧ (cell13157 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13157 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13157 ⟨13,by decide⟩).lower ∧ (cell13157 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13157 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13157 ⟨14,by decide⟩).lower ∧ (cell13157 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13157 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13157 ⟨15,by decide⟩).lower ∧ (cell13157 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13157 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13157 ⟨16,by decide⟩).lower ∧ (cell13157 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13157 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13157 ⟨17,by decide⟩).lower ∧ (cell13157 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13157 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13157 ⟨18,by decide⟩).lower ∧ (cell13157 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13157 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13157 ⟨19,by decide⟩).lower ∧ (cell13157 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13157 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13157 ⟨20,by decide⟩).lower ∧ (cell13157 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13157 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13157 ⟨21,by decide⟩).lower ∧ (cell13157 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13157 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13157 ⟨22,by decide⟩).lower ∧ (cell13157 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13157 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13157 ⟨23,by decide⟩).lower ∧ (cell13157 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13157 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13157 ⟨24,by decide⟩).lower ∧ (cell13157 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13157 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13157 ⟨25,by decide⟩).lower ∧ (cell13157 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13157 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13157 ⟨26,by decide⟩).lower ∧ (cell13157 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13157 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13157 ⟨27,by decide⟩).lower ∧ (cell13157 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13157 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13157 ⟨28,by decide⟩).lower ∧ (cell13157 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13157 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13157 ⟨29,by decide⟩).lower ∧ (cell13157 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13157 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13157 ⟨30,by decide⟩).lower ∧ (cell13157 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13157 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13157 ⟨31,by decide⟩).lower ∧ (cell13157 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13157 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13157 ⟨32,by decide⟩).lower ∧ (cell13157 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13157 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13157 ⟨33,by decide⟩).lower ∧ (cell13157 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13157 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13157 ⟨34,by decide⟩).lower ∧ (cell13157 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13157 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13157 ⟨35,by decide⟩).lower ∧ (cell13157 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13157 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13157 ⟨36,by decide⟩).lower ∧ (cell13157 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13157 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13157 ⟨37,by decide⟩).lower ∧ (cell13157 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13157 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13157 ⟨38,by decide⟩).lower ∧ (cell13157 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13157 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13157 ⟨39,by decide⟩).lower ∧ (cell13157 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13157 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13157 ⟨40,by decide⟩).lower ∧ (cell13157 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13157 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13157 ⟨41,by decide⟩).lower ∧ (cell13157 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13157 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13157 ⟨42,by decide⟩).lower ∧ (cell13157 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13157 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13157 ⟨43,by decide⟩).lower ∧ (cell13157 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13157 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13157 ⟨44,by decide⟩).lower ∧ (cell13157 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13157 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13157 ⟨45,by decide⟩).lower ∧ (cell13157 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13157 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13157 ⟨46,by decide⟩).lower ∧ (cell13157 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13157 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13157 ⟨47,by decide⟩).lower ∧ (cell13157 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13157 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13157 ⟨48,by decide⟩).lower ∧ (cell13157 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13157 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13157 ⟨49,by decide⟩).lower ∧ (cell13157 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13157 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13157 ⟨50,by decide⟩).lower ∧ (cell13157 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13157 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13157 ⟨51,by decide⟩).lower ∧ (cell13157 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13157 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13157 ⟨52,by decide⟩).lower ∧ (cell13157 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13157 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13157 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13157 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13157,cell13157,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13157 i).lower ∧
    (cell13157 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13157 i).upper ≤ (0.532 : ℝ) ∧
    (cell13157 i).centre ≤ (0.1 : ℝ) ∧ (cell13157 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13157 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13157 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13157

/-! The local source numeric instances at 13157 have no network premises. -/
namespace BstLean.Part269.N13157
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13157)
open BstLean.Part268 (cell13157)

noncomputable def sourceNumerics13157 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13157 (cell13157 i)
      scalarRow13157.M scalarRow13157.H scalarRow13157.xi := by
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
    energy_allowance := scalarRow13157.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13157]
    centre_nonneg := (scalarRow13157.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13157])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13157
/-! Actual 13158 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13158
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13158 ≤ (1.035175049633 : ℝ) := by
  have hr : (114.708325765830 : ℝ) ≤ √(13158 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.708325765830 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13158 13158 (11 / 1000) ≤
    (0.008333195475 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13158) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.708325765830 : ℝ) ≤ √(13158 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13158)
  have hdiv : K / √(13158 : ℝ) ≤ K / 114.708325765830 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.708325765830 ≤ (0.008333195475 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13158.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13158 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13158 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13158 := gPlus_lower 13158
end BstLean.Part269.N13158

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13158
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035175049632 : ℝ) ≤ wn 13158 := by
  have hn : √(13158 : ℝ) ≤ 114.708325765831 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13158 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.708325765831 ≤ 2 / √(13158 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242964624 : ℝ) ≤ rhoBar 13158 BstLean.Part154.csC ∧
    rhoBar 13158 BstLean.Part154.csC ≤ 0.000242965000 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035175049632 : ℝ) / (1.295212 * 13158) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035175049633 : ℝ) / (1.29521 * 13158) := by gcongr
      _ ≤ (0.000242965000 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13158 BstLean.Part154.csC) ≤ 0.000971919032 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13158 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13158 BstLean.Part154.csC) (piBar (rhoBar 13158 BstLean.Part154.csC)) ≤ 0.000185578000 ∧
    cc1 (rhoBar 13158 BstLean.Part154.csC) (piBar (rhoBar 13158 BstLean.Part154.csC)) ≤ 0.000118084577 ∧
    cc2 (rhoBar 13158 BstLean.Part154.csC) ≤ 0.000068549078 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13158 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13158 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13158 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13158 BstLean.Part154.csC * nuR (rhoBar 13158 BstLean.Part154.csC)) ≤ 0.000485944758 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242965000 : ℝ) * 0.000971919032 := by gcongr
      _ ≤ (0.000485944758 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13158 BstLean.Part154.csC) * nuR (rhoBar 13158 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000971919032 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13158 BstLean.Part154.csC) * rhoBar 13158 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242965000 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242965000 / 2 + 0.399 * 0.000971919032 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185578000 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485944758 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118084577 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242965000 / 1.414213562 := by gcongr
      _ ≤ (0.000068549078 : ℝ) := by norm_num

end BstLean.Part269.N13158

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13158
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13158 BstLean.Part154.csC) (piBar (rhoBar 13158 BstLean.Part154.csC)) ≤ 1.48727E-7 := by
  have hr0 : 0 ≤ rhoBar 13158 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13158 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13158 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13158 BstLean.Part154.csC) (piBar (rhoBar 13158 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13158 BstLean.Part154.csC) (piBar (rhoBar 13158 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13158 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185578000 : ℝ) ^ 2 + 0.000118084577 ^ 2 + 3 * 0.000068549078 ^ 2 +
        2 * 0.797885 * 0.000185578000 * 0.000118084577 + 2 * 0.000185578000 * 0.000068549078 +
        4 * 0.797885 * 0.000118084577 * 0.000068549078 := by gcongr
    _ ≤ (1.48727E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13158 BstLean.Part154.csC Θ ≤ 0.002534664958 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13158 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13158 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13158 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13158 BstLean.Part154.csC) (piBar (rhoBar 13158 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13158 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035175049633 * 1.48727E-7 / (0.000242964624 : ℝ) := by gcongr
    _ ≤ 0.002534664958 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13158 BstLean.Part154.csC Θ ≤ 0.002810617129 + 0.000640468415 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13158 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13158 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13158 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035175049633 : ℝ) * ((2 * Θ * 0.000242965000 +
        (6863 / 10000) * 0.000242965000 * 13158 * 0.000971919032) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002810617129 + 0.000640468415 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13158 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13158 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13158 0.011 Θ ∧ gammaRatio 13158 0.011 Θ ≤ 0.000083525085 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13158 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035175049633 : ℝ) * 0.525 / ((1 - 0.011) * 13158) := by gcongr
      _ ≤ (0.000083525085 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13158 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13158 0.011 Θ) :=
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
    badAllowance 13158 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13158 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13158 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13158 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13158 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13158 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13158 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13158 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13158 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13158 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13158 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035175049633 : ℝ) * 13158 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13158 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003127502287 + 0.003175133373 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13158

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13158
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13158 BstLean.Part154.csC) (piBar (rhoBar 13158 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13158 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13158 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13158 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13158 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13158 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13158 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13158 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13158 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13158 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13158 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13158 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13158 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13158 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13158 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051552976083 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13158) ≤ 0.010411080217 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13158 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035175049633)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010411080217 + 2 * 0.737676 / 13158) := by gcongr
    _ ≤ (0.051552976083 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13158 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13158

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13158
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523559469 : ℝ) ≤ plow 13158 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13158) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052301047308)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330699103) : eMP 13158 0.011 xi bn ≤ 0.001146205269 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13158 : ℝ) * (1 - 0.011))) ≤ 0.000566789513 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001330699103 / (13158 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566789513 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566789513 : ℝ) + 3.141593 * 0.052301047308 / (13158 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001146205269 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052301047308)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330699103) : PiBarMP 13158 12 0.011 xi bn ≤ 0.158392074798 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13158 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036478748650 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.075685402280 : ℝ) ≤ √((13158 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.708325765830 : ℝ) ≤ √(13158 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13158) ≤ 0.121459433479 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036478748650 + 0.052301047308 * 1.772454 / (2 * (114.075685402280 : ℝ))) * (1 + 0.001146205269) +
        8 / (13158 * 114.708325765830) + 0.121459433479 := by gcongr
    _ ≤ (0.158392074798 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052301047308)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330699103) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280247198372) :
    parallelOracle 13158 0.011 xi bn cd ≤ 0.159348013369 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13158 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13158 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523559469 : ℝ) ≤ plow 13158 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.708325765830 : ℝ) ≤ √(13158 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280247198372 : ℝ) / (2 * 0.560523559469 * 114.708325765830)) * 0.158392074798 +
        0.280247198372 ^ 2 / (2 * 0.560523559469 * 114.708325765830) := by gcongr
    _ ≤ (0.159348013369 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052301047308) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330699103)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280247198372) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13158 13158 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523559469 : ℝ) ≤ plow 13158 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.708325765830 : ℝ) ≤ √(13158 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13158 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13158 Θ 1.22 ≤ 0.011560629895 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.708325765830 := by gcongr <;> linarith
      _ ≤ (0.011560629895 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13158 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13158 13158 0.011 ≤ 0.008333195475 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13158 13158 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13158 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13158 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13158 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13158 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159348013369 + 0.011560629895 + (0.008333195475 : ℝ) *
        (1 + 2 * (0.280247198372 + 0.011560629895) / (0.560523559469 * 114.708325765830))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13158]

end BstLean.Part269.N13158

/-! The original eight local profiles supply actual 13158 moment certificates. -/
namespace BstLean.Part269.N13158
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13158 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13158 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13158 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052301047308 ∧
    0 ≤ bN 13158 BstLean.Part154.csC (groupTheta g) ∧ bN 13158 BstLean.Part154.csC (groupTheta g) ≤ 0.001330699103 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13158 13158 0.011
      (momentAllowance 13158 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13158 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13158 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13158 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13158 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13158 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228694222289 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13158 0.011
      (momentAllowance 13158 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13158 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13158
/-! The actual computed-centre upper energy formula at 13158. -/
namespace BstLean.Part269.N13158
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13158

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13158
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13158)
open BstLean.Part268 (cell13158)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084255986753
  | 2 => 0.085179532491
  | 3 => 0.086098536597
  | 4 => 0.087013785666
  | 5 => 0.087926248915
  | 6 => 0.088837107470
  | 7 => 0.089747786818
  | 8 => 0.090659992541
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13158 13158 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13158 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13158

/-! Actual upper energy certificates on all 43 source endpoints at 13158. -/
namespace BstLean.Part269.N13158
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13158)
open BstLean.Part268 (cell13158)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13158 (gMinus 13158) (1 - (cell13158 i).lower) ≤ 1 ∧
    energyUpper 13158 (gMinus 13158) (BstLean.Part211.gPlus 13158)
      (finiteEnergy 13158 13158 0.011) (1 - (cell13158 i).lower) ≤
      (cell13158 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨10,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨11,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨12,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨13,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨14,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨15,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨16,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨17,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨18,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨19,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨20,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨21,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨22,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨23,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨24,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨25,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨26,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨27,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨28,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨29,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨30,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨31,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨32,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨33,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨34,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨35,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨36,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨37,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨38,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨39,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨40,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨41,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨42,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨43,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨44,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨45,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨46,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨47,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨48,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨49,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨50,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨51,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13158) (by norm_num)
        (q := 1 - (cell13158 ⟨52,by decide⟩).lower)
        (by norm_num [cell13158]) (by norm_num [cell13158])
      exact ⟨E.1,E.2.trans (by norm_num [cell13158])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13158

/-! Source-cell containment and simple scalar guards at 13158. -/
namespace BstLean.Part269.N13158
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13158)
open BstLean.Part268 (cell13158)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13158 ⟨10,by decide⟩).lower ∧ (cell13158 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13158 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13158 ⟨11,by decide⟩).lower ∧ (cell13158 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13158 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13158 ⟨12,by decide⟩).lower ∧ (cell13158 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13158 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13158 ⟨13,by decide⟩).lower ∧ (cell13158 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13158 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13158 ⟨14,by decide⟩).lower ∧ (cell13158 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13158 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13158 ⟨15,by decide⟩).lower ∧ (cell13158 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13158 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13158 ⟨16,by decide⟩).lower ∧ (cell13158 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13158 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13158 ⟨17,by decide⟩).lower ∧ (cell13158 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13158 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13158 ⟨18,by decide⟩).lower ∧ (cell13158 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13158 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13158 ⟨19,by decide⟩).lower ∧ (cell13158 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13158 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13158 ⟨20,by decide⟩).lower ∧ (cell13158 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13158 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13158 ⟨21,by decide⟩).lower ∧ (cell13158 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13158 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13158 ⟨22,by decide⟩).lower ∧ (cell13158 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13158 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13158 ⟨23,by decide⟩).lower ∧ (cell13158 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13158 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13158 ⟨24,by decide⟩).lower ∧ (cell13158 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13158 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13158 ⟨25,by decide⟩).lower ∧ (cell13158 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13158 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13158 ⟨26,by decide⟩).lower ∧ (cell13158 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13158 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13158 ⟨27,by decide⟩).lower ∧ (cell13158 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13158 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13158 ⟨28,by decide⟩).lower ∧ (cell13158 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13158 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13158 ⟨29,by decide⟩).lower ∧ (cell13158 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13158 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13158 ⟨30,by decide⟩).lower ∧ (cell13158 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13158 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13158 ⟨31,by decide⟩).lower ∧ (cell13158 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13158 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13158 ⟨32,by decide⟩).lower ∧ (cell13158 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13158 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13158 ⟨33,by decide⟩).lower ∧ (cell13158 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13158 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13158 ⟨34,by decide⟩).lower ∧ (cell13158 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13158 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13158 ⟨35,by decide⟩).lower ∧ (cell13158 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13158 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13158 ⟨36,by decide⟩).lower ∧ (cell13158 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13158 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13158 ⟨37,by decide⟩).lower ∧ (cell13158 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13158 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13158 ⟨38,by decide⟩).lower ∧ (cell13158 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13158 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13158 ⟨39,by decide⟩).lower ∧ (cell13158 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13158 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13158 ⟨40,by decide⟩).lower ∧ (cell13158 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13158 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13158 ⟨41,by decide⟩).lower ∧ (cell13158 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13158 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13158 ⟨42,by decide⟩).lower ∧ (cell13158 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13158 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13158 ⟨43,by decide⟩).lower ∧ (cell13158 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13158 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13158 ⟨44,by decide⟩).lower ∧ (cell13158 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13158 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13158 ⟨45,by decide⟩).lower ∧ (cell13158 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13158 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13158 ⟨46,by decide⟩).lower ∧ (cell13158 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13158 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13158 ⟨47,by decide⟩).lower ∧ (cell13158 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13158 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13158 ⟨48,by decide⟩).lower ∧ (cell13158 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13158 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13158 ⟨49,by decide⟩).lower ∧ (cell13158 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13158 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13158 ⟨50,by decide⟩).lower ∧ (cell13158 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13158 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13158 ⟨51,by decide⟩).lower ∧ (cell13158 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13158 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13158 ⟨52,by decide⟩).lower ∧ (cell13158 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13158 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13158 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13158 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13158,cell13158,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13158 i).lower ∧
    (cell13158 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13158 i).upper ≤ (0.532 : ℝ) ∧
    (cell13158 i).centre ≤ (0.1 : ℝ) ∧ (cell13158 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13158 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13158 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13158

/-! The local source numeric instances at 13158 have no network premises. -/
namespace BstLean.Part269.N13158
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13158)
open BstLean.Part268 (cell13158)

noncomputable def sourceNumerics13158 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13158 (cell13158 i)
      scalarRow13158.M scalarRow13158.H scalarRow13158.xi := by
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
    energy_allowance := scalarRow13158.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13158]
    centre_nonneg := (scalarRow13158.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13158])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13158
/-! Actual 13159 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13159
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13159 ≤ (1.035173701517 : ℝ) := by
  have hr : (114.712684564524 : ℝ) ≤ √(13159 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.712684564524 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13159 13159 (11 / 1000) ≤
    (0.008332878832 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13159) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.712684564524 : ℝ) ≤ √(13159 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13159)
  have hdiv : K / √(13159 : ℝ) ≤ K / 114.712684564524 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.712684564524 ≤ (0.008332878832 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13159.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13159 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13159 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13159 := gPlus_lower 13159
end BstLean.Part269.N13159

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13159
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035173701516 : ℝ) ≤ wn 13159 := by
  have hn : √(13159 : ℝ) ≤ 114.712684564525 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13159 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.712684564525 ≤ 2 / √(13159 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242945844 : ℝ) ≤ rhoBar 13159 BstLean.Part154.csC ∧
    rhoBar 13159 BstLean.Part154.csC ≤ 0.000242946220 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035173701516 : ℝ) / (1.295212 * 13159) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035173701517 : ℝ) / (1.29521 * 13159) := by gcongr
      _ ≤ (0.000242946220 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13159 BstLean.Part154.csC) ≤ 0.000971843903 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13159 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13159 BstLean.Part154.csC) (piBar (rhoBar 13159 BstLean.Part154.csC)) ≤ 0.000185563656 ∧
    cc1 (rhoBar 13159 BstLean.Part154.csC) (piBar (rhoBar 13159 BstLean.Part154.csC)) ≤ 0.000118075449 ∧
    cc2 (rhoBar 13159 BstLean.Part154.csC) ≤ 0.000068543779 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13159 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13159 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13159 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13159 BstLean.Part154.csC * nuR (rhoBar 13159 BstLean.Part154.csC)) ≤ 0.000485907196 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242946220 : ℝ) * 0.000971843903 := by gcongr
      _ ≤ (0.000485907196 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13159 BstLean.Part154.csC) * nuR (rhoBar 13159 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000971843903 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13159 BstLean.Part154.csC) * rhoBar 13159 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242946220 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242946220 / 2 + 0.399 * 0.000971843903 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185563656 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485907196 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118075449 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242946220 / 1.414213562 := by gcongr
      _ ≤ (0.000068543779 : ℝ) := by norm_num

end BstLean.Part269.N13159

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13159
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13159 BstLean.Part154.csC) (piBar (rhoBar 13159 BstLean.Part154.csC)) ≤ 1.48704E-7 := by
  have hr0 : 0 ≤ rhoBar 13159 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13159 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13159 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13159 BstLean.Part154.csC) (piBar (rhoBar 13159 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13159 BstLean.Part154.csC) (piBar (rhoBar 13159 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13159 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185563656 : ℝ) ^ 2 + 0.000118075449 ^ 2 + 3 * 0.000068543779 ^ 2 +
        2 * 0.797885 * 0.000185563656 * 0.000118075449 + 2 * 0.000185563656 * 0.000068543779 +
        4 * 0.797885 * 0.000118075449 * 0.000068543779 := by gcongr
    _ ≤ (1.48704E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13159 BstLean.Part154.csC Θ ≤ 0.002534465585 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13159 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13159 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13159 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13159 BstLean.Part154.csC) (piBar (rhoBar 13159 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13159 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035173701517 * 1.48704E-7 / (0.000242945844 : ℝ) := by gcongr
    _ ≤ 0.002534465585 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13159 BstLean.Part154.csC Θ ≤ 0.002810392552 + 0.000640418076 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13159 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13159 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13159 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035173701517 : ℝ) * ((2 * Θ * 0.000242946220 +
        (6863 / 10000) * 0.000242946220 * 13159 * 0.000971843903) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002810392552 + 0.000640418076 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13159 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13159 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13159 0.011 Θ ∧ gammaRatio 13159 0.011 Θ ≤ 0.000083518628 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13159 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035173701517 : ℝ) * 0.525 / ((1 - 0.011) * 13159) := by gcongr
      _ ≤ (0.000083518628 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13159 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13159 0.011 Θ) :=
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
    badAllowance 13159 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13159 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13159 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13159 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13159 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13159 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13159 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13159 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13159 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13159 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13159 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035173701517 : ℝ) * 13159 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13159 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003127277710 + 0.003174883661 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13159

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13159
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13159 BstLean.Part154.csC) (piBar (rhoBar 13159 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13159 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13159 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13159 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13159 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13159 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13159 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13159 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13159 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13159 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13159 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13159 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13159 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13159 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13159 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051550996328 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13159) ≤ 0.010410684622 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13159 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035173701517)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010410684622 + 2 * 0.737676 / 13159) := by gcongr
    _ ≤ (0.051550996328 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13159 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13159

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13159
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523601595 : ℝ) ≤ plow 13159 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13159) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052300691633)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330594433) : eMP 13159 0.011 xi bn ≤ 0.001146116568 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13159 : ℝ) * (1 - 0.011))) ≤ 0.000566745685 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001330594433 / (13159 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566745685 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566745685 : ℝ) + 3.141593 * 0.052300691633 / (13159 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001146116568 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052300691633)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330594433) : PiBarMP 13159 12 0.011 xi bn ≤ 0.158386001196 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13159 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036477313950 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.080020161288 : ℝ) ≤ √((13159 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.712684564524 : ℝ) ≤ √(13159 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13159) ≤ 0.121454818320 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036477313950 + 0.052300691633 * 1.772454 / (2 * (114.080020161288 : ℝ))) * (1 + 0.001146116568) +
        8 / (13159 * 114.712684564524) + 0.121454818320 := by gcongr
    _ ≤ (0.158386001196 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052300691633)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330594433) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280244440994) :
    parallelOracle 13159 0.011 xi bn cd ≤ 0.159341874722 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13159 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13159 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523601595 : ℝ) ≤ plow 13159 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.712684564524 : ℝ) ≤ √(13159 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280244440994 : ℝ) / (2 * 0.560523601595 * 114.712684564524)) * 0.158386001196 +
        0.280244440994 ^ 2 / (2 * 0.560523601595 * 114.712684564524) := by gcongr
    _ ≤ (0.159341874722 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052300691633) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330594433)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280244440994) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13159 13159 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523601595 : ℝ) ≤ plow 13159 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.712684564524 : ℝ) ≤ √(13159 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13159 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13159 Θ 1.22 ≤ 0.011560190620 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.712684564524 := by gcongr <;> linarith
      _ ≤ (0.011560190620 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13159 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13159 13159 0.011 ≤ 0.008332878832 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13159 13159 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13159 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13159 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13159 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13159 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159341874722 + 0.011560190620 + (0.008332878832 : ℝ) *
        (1 + 2 * (0.280244440994 + 0.011560190620) / (0.560523601595 * 114.712684564524))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13159]

end BstLean.Part269.N13159

/-! The original eight local profiles supply actual 13159 moment certificates. -/
namespace BstLean.Part269.N13159
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13159 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13159 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13159 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052300691633 ∧
    0 ≤ bN 13159 BstLean.Part154.csC (groupTheta g) ∧ bN 13159 BstLean.Part154.csC (groupTheta g) ≤ 0.001330594433 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13159 13159 0.011
      (momentAllowance 13159 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13159 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13159 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13159 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13159 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13159 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228693444666 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13159 0.011
      (momentAllowance 13159 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13159 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13159
/-! The actual computed-centre upper energy formula at 13159. -/
namespace BstLean.Part269.N13159
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13159

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13159
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13159)
open BstLean.Part268 (cell13159)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084253487360
  | 2 => 0.085177002627
  | 3 => 0.086095971990
  | 4 => 0.087011181018
  | 5 => 0.087923597715
  | 6 => 0.088834401772
  | 7 => 0.089745016997
  | 8 => 0.090657147021
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13159 13159 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13159 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13159

/-! Actual upper energy certificates on all 43 source endpoints at 13159. -/
namespace BstLean.Part269.N13159
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13159)
open BstLean.Part268 (cell13159)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13159 (gMinus 13159) (1 - (cell13159 i).lower) ≤ 1 ∧
    energyUpper 13159 (gMinus 13159) (BstLean.Part211.gPlus 13159)
      (finiteEnergy 13159 13159 0.011) (1 - (cell13159 i).lower) ≤
      (cell13159 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨10,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨11,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨12,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨13,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨14,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨15,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨16,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨17,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨18,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨19,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨20,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨21,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨22,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨23,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨24,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨25,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨26,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨27,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨28,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨29,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨30,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨31,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨32,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨33,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨34,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨35,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨36,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨37,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨38,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨39,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨40,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨41,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨42,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨43,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨44,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨45,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨46,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨47,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨48,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨49,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨50,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨51,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13159) (by norm_num)
        (q := 1 - (cell13159 ⟨52,by decide⟩).lower)
        (by norm_num [cell13159]) (by norm_num [cell13159])
      exact ⟨E.1,E.2.trans (by norm_num [cell13159])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13159

/-! Source-cell containment and simple scalar guards at 13159. -/
namespace BstLean.Part269.N13159
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13159)
open BstLean.Part268 (cell13159)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13159 ⟨10,by decide⟩).lower ∧ (cell13159 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13159 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13159 ⟨11,by decide⟩).lower ∧ (cell13159 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13159 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13159 ⟨12,by decide⟩).lower ∧ (cell13159 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13159 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13159 ⟨13,by decide⟩).lower ∧ (cell13159 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13159 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13159 ⟨14,by decide⟩).lower ∧ (cell13159 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13159 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13159 ⟨15,by decide⟩).lower ∧ (cell13159 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13159 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13159 ⟨16,by decide⟩).lower ∧ (cell13159 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13159 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13159 ⟨17,by decide⟩).lower ∧ (cell13159 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13159 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13159 ⟨18,by decide⟩).lower ∧ (cell13159 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13159 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13159 ⟨19,by decide⟩).lower ∧ (cell13159 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13159 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13159 ⟨20,by decide⟩).lower ∧ (cell13159 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13159 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13159 ⟨21,by decide⟩).lower ∧ (cell13159 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13159 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13159 ⟨22,by decide⟩).lower ∧ (cell13159 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13159 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13159 ⟨23,by decide⟩).lower ∧ (cell13159 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13159 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13159 ⟨24,by decide⟩).lower ∧ (cell13159 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13159 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13159 ⟨25,by decide⟩).lower ∧ (cell13159 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13159 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13159 ⟨26,by decide⟩).lower ∧ (cell13159 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13159 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13159 ⟨27,by decide⟩).lower ∧ (cell13159 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13159 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13159 ⟨28,by decide⟩).lower ∧ (cell13159 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13159 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13159 ⟨29,by decide⟩).lower ∧ (cell13159 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13159 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13159 ⟨30,by decide⟩).lower ∧ (cell13159 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13159 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13159 ⟨31,by decide⟩).lower ∧ (cell13159 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13159 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13159 ⟨32,by decide⟩).lower ∧ (cell13159 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13159 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13159 ⟨33,by decide⟩).lower ∧ (cell13159 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13159 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13159 ⟨34,by decide⟩).lower ∧ (cell13159 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13159 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13159 ⟨35,by decide⟩).lower ∧ (cell13159 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13159 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13159 ⟨36,by decide⟩).lower ∧ (cell13159 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13159 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13159 ⟨37,by decide⟩).lower ∧ (cell13159 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13159 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13159 ⟨38,by decide⟩).lower ∧ (cell13159 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13159 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13159 ⟨39,by decide⟩).lower ∧ (cell13159 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13159 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13159 ⟨40,by decide⟩).lower ∧ (cell13159 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13159 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13159 ⟨41,by decide⟩).lower ∧ (cell13159 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13159 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13159 ⟨42,by decide⟩).lower ∧ (cell13159 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13159 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13159 ⟨43,by decide⟩).lower ∧ (cell13159 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13159 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13159 ⟨44,by decide⟩).lower ∧ (cell13159 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13159 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13159 ⟨45,by decide⟩).lower ∧ (cell13159 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13159 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13159 ⟨46,by decide⟩).lower ∧ (cell13159 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13159 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13159 ⟨47,by decide⟩).lower ∧ (cell13159 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13159 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13159 ⟨48,by decide⟩).lower ∧ (cell13159 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13159 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13159 ⟨49,by decide⟩).lower ∧ (cell13159 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13159 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13159 ⟨50,by decide⟩).lower ∧ (cell13159 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13159 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13159 ⟨51,by decide⟩).lower ∧ (cell13159 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13159 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13159 ⟨52,by decide⟩).lower ∧ (cell13159 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13159 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13159 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13159 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13159,cell13159,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13159 i).lower ∧
    (cell13159 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13159 i).upper ≤ (0.532 : ℝ) ∧
    (cell13159 i).centre ≤ (0.1 : ℝ) ∧ (cell13159 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13159 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13159 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13159

/-! The local source numeric instances at 13159 have no network premises. -/
namespace BstLean.Part269.N13159
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13159)
open BstLean.Part268 (cell13159)

noncomputable def sourceNumerics13159 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13159 (cell13159 i)
      scalarRow13159.M scalarRow13159.H scalarRow13159.xi := by
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
    energy_allowance := scalarRow13159.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13159]
    centre_nonneg := (scalarRow13159.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13159])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13159
/-! Actual 13160 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13160
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13160 ≤ (1.035172353556 : ℝ) := by
  have hr : (114.717043197599 : ℝ) ≤ √(13160 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.717043197599 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13160 13160 (11 / 1000) ≤
    (0.008332562225 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13160) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.717043197599 : ℝ) ≤ √(13160 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13160)
  have hdiv : K / √(13160 : ℝ) ≤ K / 114.717043197599 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.717043197599 ≤ (0.008332562225 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13160.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13160 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13160 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13160 := gPlus_lower 13160
end BstLean.Part269.N13160

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13160
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035172353555 : ℝ) ≤ wn 13160 := by
  have hn : √(13160 : ℝ) ≤ 114.717043197600 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13160 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.717043197600 ≤ 2 / √(13160 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242927067 : ℝ) ≤ rhoBar 13160 BstLean.Part154.csC ∧
    rhoBar 13160 BstLean.Part154.csC ≤ 0.000242927443 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035172353555 : ℝ) / (1.295212 * 13160) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035172353556 : ℝ) / (1.29521 * 13160) := by gcongr
      _ ≤ (0.000242927443 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13160 BstLean.Part154.csC) ≤ 0.000971768786 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13160 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13160 BstLean.Part154.csC) (piBar (rhoBar 13160 BstLean.Part154.csC)) ≤ 0.000185549313 ∧
    cc1 (rhoBar 13160 BstLean.Part154.csC) (piBar (rhoBar 13160 BstLean.Part154.csC)) ≤ 0.000118066323 ∧
    cc2 (rhoBar 13160 BstLean.Part154.csC) ≤ 0.000068538482 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13160 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13160 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13160 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13160 BstLean.Part154.csC * nuR (rhoBar 13160 BstLean.Part154.csC)) ≤ 0.000485869640 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242927443 : ℝ) * 0.000971768786 := by gcongr
      _ ≤ (0.000485869640 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13160 BstLean.Part154.csC) * nuR (rhoBar 13160 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000971768786 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13160 BstLean.Part154.csC) * rhoBar 13160 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242927443 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242927443 / 2 + 0.399 * 0.000971768786 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185549313 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485869640 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118066323 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242927443 / 1.414213562 := by gcongr
      _ ≤ (0.000068538482 : ℝ) := by norm_num

end BstLean.Part269.N13160

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13160
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13160 BstLean.Part154.csC) (piBar (rhoBar 13160 BstLean.Part154.csC)) ≤ 1.48681E-7 := by
  have hr0 : 0 ≤ rhoBar 13160 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13160 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13160 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13160 BstLean.Part154.csC) (piBar (rhoBar 13160 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13160 BstLean.Part154.csC) (piBar (rhoBar 13160 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13160 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185549313 : ℝ) ^ 2 + 0.000118066323 ^ 2 + 3 * 0.000068538482 ^ 2 +
        2 * 0.797885 * 0.000185549313 * 0.000118066323 + 2 * 0.000185549313 * 0.000068538482 +
        4 * 0.797885 * 0.000118066323 * 0.000068538482 := by gcongr
    _ ≤ (1.48681E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13160 BstLean.Part154.csC Θ ≤ 0.002534266150 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13160 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13160 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13160 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13160 BstLean.Part154.csC) (piBar (rhoBar 13160 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13160 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035172353556 * 1.48681E-7 / (0.000242927067 : ℝ) := by gcongr
    _ ≤ 0.002534266150 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13160 BstLean.Part154.csC Θ ≤ 0.002810168012 + 0.000640367745 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13160 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13160 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13160 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035172353556 : ℝ) * ((2 * Θ * 0.000242927443 +
        (6863 / 10000) * 0.000242927443 * 13160 * 0.000971768786) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002810168012 + 0.000640367745 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13160 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13160 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13160 0.011 Θ ∧ gammaRatio 13160 0.011 Θ ≤ 0.000083512173 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13160 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035172353556 : ℝ) * 0.525 / ((1 - 0.011) * 13160) := by gcongr
      _ ≤ (0.000083512173 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13160 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13160 0.011 Θ) :=
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
    badAllowance 13160 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13160 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13160 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13160 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13160 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13160 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13160 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13160 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13160 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13160 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13160 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035172353556 : ℝ) * 13160 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13160 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003127053170 + 0.003174633895 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13160

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13160
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13160 BstLean.Part154.csC) (piBar (rhoBar 13160 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13160 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13160 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13160 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13160 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13160 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13160 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13160 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13160 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13160 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13160 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13160 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13160 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13160 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13160 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051549016794 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13160) ≤ 0.010410289071 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13160 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035172353556)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010410289071 + 2 * 0.737676 / 13160) := by gcongr
    _ ≤ (0.051549016794 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13160 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13160

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13160
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523643715 : ℝ) ≤ plow 13160 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13160) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052300335965)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330489729) : eMP 13160 0.011 xi bn ≤ 0.001146027861 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13160 : ℝ) * (1 - 0.011))) ≤ 0.000566701854 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001330489729 / (13160 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566701854 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566701854 : ℝ) + 3.141593 * 0.052300335965 / (13160 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001146027861 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052300335965)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330489729) : PiBarMP 13160 12 0.011 xi bn ≤ 0.158379927602 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13160 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036475878729 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.084354755593 : ℝ) ≤ √((13160 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.717043197599 : ℝ) ≤ √(13160 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13160) ≤ 0.121450203688 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036475878729 + 0.052300335965 * 1.772454 / (2 * (114.084354755593 : ℝ))) * (1 + 0.001146027861) +
        8 / (13160 * 114.717043197599) + 0.121450203688 := by gcongr
    _ ≤ (0.158379927602 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052300335965)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330489729) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280241683850) :
    parallelOracle 13160 0.011 xi bn cd ≤ 0.159335736091 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13160 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13160 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523643715 : ℝ) ≤ plow 13160 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.717043197599 : ℝ) ≤ √(13160 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280241683850 : ℝ) / (2 * 0.560523643715 * 114.717043197599)) * 0.158379927602 +
        0.280241683850 ^ 2 / (2 * 0.560523643715 * 114.717043197599) := by gcongr
    _ ≤ (0.159335736091 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052300335965) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330489729)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280241683850) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13160 13160 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523643715 : ℝ) ≤ plow 13160 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.717043197599 : ℝ) ≤ √(13160 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13160 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13160 Θ 1.22 ≤ 0.011559751394 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.717043197599 := by gcongr <;> linarith
      _ ≤ (0.011559751394 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13160 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13160 13160 0.011 ≤ 0.008332562225 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13160 13160 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13160 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13160 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13160 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13160 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159335736091 + 0.011559751394 + (0.008332562225 : ℝ) *
        (1 + 2 * (0.280241683850 + 0.011559751394) / (0.560523643715 * 114.717043197599))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13160]

end BstLean.Part269.N13160

/-! The original eight local profiles supply actual 13160 moment certificates. -/
namespace BstLean.Part269.N13160
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13160 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13160 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13160 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052300335965 ∧
    0 ≤ bN 13160 BstLean.Part154.csC (groupTheta g) ∧ bN 13160 BstLean.Part154.csC (groupTheta g) ≤ 0.001330489729 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13160 13160 0.011
      (momentAllowance 13160 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13160 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13160 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13160 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13160 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13160 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228692667056 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13160 0.011
      (momentAllowance 13160 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13160 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13160
/-! The actual computed-centre upper energy formula at 13160. -/
namespace BstLean.Part269.N13160
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13160

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13160
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13160)
open BstLean.Part268 (cell13160)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084250988668
  | 2 => 0.085174473487
  | 3 => 0.086093408135
  | 4 => 0.087008577159
  | 5 => 0.087920947347
  | 6 => 0.088831696960
  | 7 => 0.089742248128
  | 8 => 0.090654302531
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13160 13160 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13160 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13160

/-! Actual upper energy certificates on all 43 source endpoints at 13160. -/
namespace BstLean.Part269.N13160
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13160)
open BstLean.Part268 (cell13160)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13160 (gMinus 13160) (1 - (cell13160 i).lower) ≤ 1 ∧
    energyUpper 13160 (gMinus 13160) (BstLean.Part211.gPlus 13160)
      (finiteEnergy 13160 13160 0.011) (1 - (cell13160 i).lower) ≤
      (cell13160 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨10,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨11,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨12,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨13,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨14,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨15,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨16,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨17,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨18,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨19,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨20,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨21,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨22,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨23,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨24,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨25,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨26,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨27,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨28,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨29,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨30,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨31,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨32,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨33,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨34,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨35,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨36,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨37,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨38,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨39,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨40,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨41,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨42,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨43,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨44,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨45,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨46,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨47,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨48,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨49,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨50,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨51,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13160) (by norm_num)
        (q := 1 - (cell13160 ⟨52,by decide⟩).lower)
        (by norm_num [cell13160]) (by norm_num [cell13160])
      exact ⟨E.1,E.2.trans (by norm_num [cell13160])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13160

/-! Source-cell containment and simple scalar guards at 13160. -/
namespace BstLean.Part269.N13160
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13160)
open BstLean.Part268 (cell13160)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13160 ⟨10,by decide⟩).lower ∧ (cell13160 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13160 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13160 ⟨11,by decide⟩).lower ∧ (cell13160 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13160 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13160 ⟨12,by decide⟩).lower ∧ (cell13160 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13160 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13160 ⟨13,by decide⟩).lower ∧ (cell13160 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13160 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13160 ⟨14,by decide⟩).lower ∧ (cell13160 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13160 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13160 ⟨15,by decide⟩).lower ∧ (cell13160 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13160 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13160 ⟨16,by decide⟩).lower ∧ (cell13160 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13160 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13160 ⟨17,by decide⟩).lower ∧ (cell13160 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13160 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13160 ⟨18,by decide⟩).lower ∧ (cell13160 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13160 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13160 ⟨19,by decide⟩).lower ∧ (cell13160 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13160 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13160 ⟨20,by decide⟩).lower ∧ (cell13160 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13160 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13160 ⟨21,by decide⟩).lower ∧ (cell13160 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13160 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13160 ⟨22,by decide⟩).lower ∧ (cell13160 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13160 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13160 ⟨23,by decide⟩).lower ∧ (cell13160 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13160 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13160 ⟨24,by decide⟩).lower ∧ (cell13160 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13160 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13160 ⟨25,by decide⟩).lower ∧ (cell13160 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13160 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13160 ⟨26,by decide⟩).lower ∧ (cell13160 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13160 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13160 ⟨27,by decide⟩).lower ∧ (cell13160 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13160 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13160 ⟨28,by decide⟩).lower ∧ (cell13160 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13160 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13160 ⟨29,by decide⟩).lower ∧ (cell13160 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13160 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13160 ⟨30,by decide⟩).lower ∧ (cell13160 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13160 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13160 ⟨31,by decide⟩).lower ∧ (cell13160 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13160 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13160 ⟨32,by decide⟩).lower ∧ (cell13160 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13160 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13160 ⟨33,by decide⟩).lower ∧ (cell13160 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13160 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13160 ⟨34,by decide⟩).lower ∧ (cell13160 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13160 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13160 ⟨35,by decide⟩).lower ∧ (cell13160 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13160 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13160 ⟨36,by decide⟩).lower ∧ (cell13160 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13160 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13160 ⟨37,by decide⟩).lower ∧ (cell13160 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13160 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13160 ⟨38,by decide⟩).lower ∧ (cell13160 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13160 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13160 ⟨39,by decide⟩).lower ∧ (cell13160 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13160 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13160 ⟨40,by decide⟩).lower ∧ (cell13160 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13160 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13160 ⟨41,by decide⟩).lower ∧ (cell13160 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13160 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13160 ⟨42,by decide⟩).lower ∧ (cell13160 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13160 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13160 ⟨43,by decide⟩).lower ∧ (cell13160 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13160 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13160 ⟨44,by decide⟩).lower ∧ (cell13160 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13160 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13160 ⟨45,by decide⟩).lower ∧ (cell13160 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13160 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13160 ⟨46,by decide⟩).lower ∧ (cell13160 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13160 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13160 ⟨47,by decide⟩).lower ∧ (cell13160 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13160 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13160 ⟨48,by decide⟩).lower ∧ (cell13160 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13160 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13160 ⟨49,by decide⟩).lower ∧ (cell13160 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13160 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13160 ⟨50,by decide⟩).lower ∧ (cell13160 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13160 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13160 ⟨51,by decide⟩).lower ∧ (cell13160 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13160 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13160 ⟨52,by decide⟩).lower ∧ (cell13160 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13160 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13160 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13160 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13160,cell13160,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13160 i).lower ∧
    (cell13160 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13160 i).upper ≤ (0.532 : ℝ) ∧
    (cell13160 i).centre ≤ (0.1 : ℝ) ∧ (cell13160 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13160 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13160 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13160

/-! The local source numeric instances at 13160 have no network premises. -/
namespace BstLean.Part269.N13160
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13160)
open BstLean.Part268 (cell13160)

noncomputable def sourceNumerics13160 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13160 (cell13160 i)
      scalarRow13160.M scalarRow13160.H scalarRow13160.xi := by
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
    energy_allowance := scalarRow13160.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13160]
    centre_nonneg := (scalarRow13160.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13160])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13160
/-! Actual 13161 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13161
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13161 ≤ (1.035171005749 : ℝ) := by
  have hr : (114.721401665077 : ℝ) ≤ √(13161 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.721401665077 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13161 13161 (11 / 1000) ≤
    (0.008332245654 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13161) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.721401665077 : ℝ) ≤ √(13161 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13161)
  have hdiv : K / √(13161 : ℝ) ≤ K / 114.721401665077 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.721401665077 ≤ (0.008332245654 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13161.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13161 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13161 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13161 := gPlus_lower 13161
end BstLean.Part269.N13161

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13161
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035171005748 : ℝ) ≤ wn 13161 := by
  have hn : √(13161 : ℝ) ≤ 114.721401665078 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13161 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.721401665078 ≤ 2 / √(13161 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242908292 : ℝ) ≤ rhoBar 13161 BstLean.Part154.csC ∧
    rhoBar 13161 BstLean.Part154.csC ≤ 0.000242908669 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035171005748 : ℝ) / (1.295212 * 13161) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035171005749 : ℝ) / (1.29521 * 13161) := by gcongr
      _ ≤ (0.000242908669 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13161 BstLean.Part154.csC) ≤ 0.000971693681 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13161 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13161 BstLean.Part154.csC) (piBar (rhoBar 13161 BstLean.Part154.csC)) ≤ 0.000185534973 ∧
    cc1 (rhoBar 13161 BstLean.Part154.csC) (piBar (rhoBar 13161 BstLean.Part154.csC)) ≤ 0.000118057198 ∧
    cc2 (rhoBar 13161 BstLean.Part154.csC) ≤ 0.000068533185 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13161 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13161 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13161 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13161 BstLean.Part154.csC * nuR (rhoBar 13161 BstLean.Part154.csC)) ≤ 0.000485832090 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242908669 : ℝ) * 0.000971693681 := by gcongr
      _ ≤ (0.000485832090 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13161 BstLean.Part154.csC) * nuR (rhoBar 13161 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000971693681 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13161 BstLean.Part154.csC) * rhoBar 13161 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242908669 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242908669 / 2 + 0.399 * 0.000971693681 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185534973 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485832090 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118057198 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242908669 / 1.414213562 := by gcongr
      _ ≤ (0.000068533185 : ℝ) := by norm_num

end BstLean.Part269.N13161

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13161
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13161 BstLean.Part154.csC) (piBar (rhoBar 13161 BstLean.Part154.csC)) ≤ 1.48658E-7 := by
  have hr0 : 0 ≤ rhoBar 13161 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13161 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13161 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13161 BstLean.Part154.csC) (piBar (rhoBar 13161 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13161 BstLean.Part154.csC) (piBar (rhoBar 13161 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13161 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185534973 : ℝ) ^ 2 + 0.000118057198 ^ 2 + 3 * 0.000068533185 ^ 2 +
        2 * 0.797885 * 0.000185534973 * 0.000118057198 + 2 * 0.000185534973 * 0.000068533185 +
        4 * 0.797885 * 0.000118057198 * 0.000068533185 := by gcongr
    _ ≤ (1.48658E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13161 BstLean.Part154.csC Θ ≤ 0.002534066666 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13161 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13161 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13161 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13161 BstLean.Part154.csC) (piBar (rhoBar 13161 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13161 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035171005749 * 1.48658E-7 / (0.000242908292 : ℝ) := by gcongr
    _ ≤ 0.002534066666 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13161 BstLean.Part154.csC Θ ≤ 0.002809943510 + 0.000640317422 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13161 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13161 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13161 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035171005749 : ℝ) * ((2 * Θ * 0.000242908669 +
        (6863 / 10000) * 0.000242908669 * 13161 * 0.000971693681) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002809943510 + 0.000640317422 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13161 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13161 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13161 0.011 Θ ∧ gammaRatio 13161 0.011 Θ ≤ 0.000083505719 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13161 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035171005749 : ℝ) * 0.525 / ((1 - 0.011) * 13161) := by gcongr
      _ ≤ (0.000083505719 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13161 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13161 0.011 Θ) :=
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
    badAllowance 13161 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13161 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13161 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13161 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13161 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13161 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13161 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13161 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13161 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13161 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13161 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035171005749 : ℝ) * 13161 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13161 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003126828668 + 0.003174384088 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13161

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13161
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13161 BstLean.Part154.csC) (piBar (rhoBar 13161 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13161 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13161 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13161 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13161 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13161 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13161 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13161 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13161 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13161 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13161 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13161 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13161 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13161 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13161 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051547037492 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13161) ≤ 0.010409893566 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13161 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035171005749)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010409893566 + 2 * 0.737676 / 13161) := by gcongr
    _ ≤ (0.051547037492 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13161 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13161

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13161
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523685829 : ℝ) ≤ plow 13161 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13161) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052299980315)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330385000) : eMP 13161 0.011 xi bn ≤ 0.001145939148 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13161 : ℝ) * (1 - 0.011))) ≤ 0.000566658020 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001330385000 / (13161 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566658020 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566658020 : ℝ) + 3.141593 * 0.052299980315 / (13161 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001145939148 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052299980315)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330385000) : PiBarMP 13161 12 0.011 xi bn ≤ 0.158373854134 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13161 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036474443108 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.088689185212 : ℝ) ≤ √((13161 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.721401665077 : ℝ) ≤ √(13161 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13161) ≤ 0.121445589581 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036474443108 + 0.052299980315 * 1.772454 / (2 * (114.088689185212 : ℝ))) * (1 + 0.001145939148) +
        8 / (13161 * 114.721401665077) + 0.121445589581 := by gcongr
    _ ≤ (0.158373854134 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052299980315)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330385000) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280238926975) :
    parallelOracle 13161 0.011 xi bn cd ≤ 0.159329597594 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13161 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13161 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523685829 : ℝ) ≤ plow 13161 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.721401665077 : ℝ) ≤ √(13161 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280238926975 : ℝ) / (2 * 0.560523685829 * 114.721401665077)) * 0.158373854134 +
        0.280238926975 ^ 2 / (2 * 0.560523685829 * 114.721401665077) := by gcongr
    _ ≤ (0.159329597594 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052299980315) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330385000)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280238926975) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13161 13161 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523685829 : ℝ) ≤ plow 13161 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.721401665077 : ℝ) ≤ √(13161 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13161 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13161 Θ 1.22 ≤ 0.011559312219 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.721401665077 := by gcongr <;> linarith
      _ ≤ (0.011559312219 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13161 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13161 13161 0.011 ≤ 0.008332245654 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13161 13161 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13161 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13161 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13161 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13161 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159329597594 + 0.011559312219 + (0.008332245654 : ℝ) *
        (1 + 2 * (0.280238926975 + 0.011559312219) / (0.560523685829 * 114.721401665077))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13161]

end BstLean.Part269.N13161

/-! The original eight local profiles supply actual 13161 moment certificates. -/
namespace BstLean.Part269.N13161
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13161 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13161 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13161 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052299980315 ∧
    0 ≤ bN 13161 BstLean.Part154.csC (groupTheta g) ∧ bN 13161 BstLean.Part154.csC (groupTheta g) ≤ 0.001330385000 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13161 13161 0.011
      (momentAllowance 13161 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13161 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13161 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13161 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13161 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13161 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228691889483 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13161 0.011
      (momentAllowance 13161 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13161 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13161
/-! The actual computed-centre upper energy formula at 13161. -/
namespace BstLean.Part269.N13161
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13161

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13161
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13161)
open BstLean.Part268 (cell13161)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084248490674
  | 2 => 0.085171945069
  | 3 => 0.086090845032
  | 4 => 0.087005974087
  | 5 => 0.087918297810
  | 6 => 0.088828993031
  | 7 => 0.089739480208
  | 8 => 0.090651459069
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13161 13161 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13161 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13161

/-! Actual upper energy certificates on all 43 source endpoints at 13161. -/
namespace BstLean.Part269.N13161
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13161)
open BstLean.Part268 (cell13161)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13161 (gMinus 13161) (1 - (cell13161 i).lower) ≤ 1 ∧
    energyUpper 13161 (gMinus 13161) (BstLean.Part211.gPlus 13161)
      (finiteEnergy 13161 13161 0.011) (1 - (cell13161 i).lower) ≤
      (cell13161 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨10,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨11,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨12,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨13,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨14,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨15,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨16,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨17,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨18,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨19,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨20,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨21,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨22,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨23,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨24,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨25,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨26,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨27,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨28,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨29,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨30,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨31,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨32,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨33,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨34,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨35,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨36,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨37,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨38,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨39,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨40,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨41,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨42,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨43,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨44,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨45,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨46,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨47,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨48,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨49,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨50,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨51,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13161) (by norm_num)
        (q := 1 - (cell13161 ⟨52,by decide⟩).lower)
        (by norm_num [cell13161]) (by norm_num [cell13161])
      exact ⟨E.1,E.2.trans (by norm_num [cell13161])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13161

/-! Source-cell containment and simple scalar guards at 13161. -/
namespace BstLean.Part269.N13161
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13161)
open BstLean.Part268 (cell13161)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13161 ⟨10,by decide⟩).lower ∧ (cell13161 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13161 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13161 ⟨11,by decide⟩).lower ∧ (cell13161 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13161 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13161 ⟨12,by decide⟩).lower ∧ (cell13161 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13161 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13161 ⟨13,by decide⟩).lower ∧ (cell13161 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13161 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13161 ⟨14,by decide⟩).lower ∧ (cell13161 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13161 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13161 ⟨15,by decide⟩).lower ∧ (cell13161 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13161 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13161 ⟨16,by decide⟩).lower ∧ (cell13161 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13161 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13161 ⟨17,by decide⟩).lower ∧ (cell13161 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13161 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13161 ⟨18,by decide⟩).lower ∧ (cell13161 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13161 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13161 ⟨19,by decide⟩).lower ∧ (cell13161 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13161 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13161 ⟨20,by decide⟩).lower ∧ (cell13161 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13161 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13161 ⟨21,by decide⟩).lower ∧ (cell13161 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13161 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13161 ⟨22,by decide⟩).lower ∧ (cell13161 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13161 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13161 ⟨23,by decide⟩).lower ∧ (cell13161 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13161 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13161 ⟨24,by decide⟩).lower ∧ (cell13161 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13161 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13161 ⟨25,by decide⟩).lower ∧ (cell13161 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13161 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13161 ⟨26,by decide⟩).lower ∧ (cell13161 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13161 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13161 ⟨27,by decide⟩).lower ∧ (cell13161 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13161 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13161 ⟨28,by decide⟩).lower ∧ (cell13161 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13161 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13161 ⟨29,by decide⟩).lower ∧ (cell13161 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13161 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13161 ⟨30,by decide⟩).lower ∧ (cell13161 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13161 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13161 ⟨31,by decide⟩).lower ∧ (cell13161 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13161 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13161 ⟨32,by decide⟩).lower ∧ (cell13161 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13161 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13161 ⟨33,by decide⟩).lower ∧ (cell13161 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13161 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13161 ⟨34,by decide⟩).lower ∧ (cell13161 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13161 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13161 ⟨35,by decide⟩).lower ∧ (cell13161 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13161 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13161 ⟨36,by decide⟩).lower ∧ (cell13161 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13161 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13161 ⟨37,by decide⟩).lower ∧ (cell13161 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13161 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13161 ⟨38,by decide⟩).lower ∧ (cell13161 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13161 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13161 ⟨39,by decide⟩).lower ∧ (cell13161 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13161 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13161 ⟨40,by decide⟩).lower ∧ (cell13161 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13161 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13161 ⟨41,by decide⟩).lower ∧ (cell13161 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13161 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13161 ⟨42,by decide⟩).lower ∧ (cell13161 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13161 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13161 ⟨43,by decide⟩).lower ∧ (cell13161 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13161 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13161 ⟨44,by decide⟩).lower ∧ (cell13161 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13161 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13161 ⟨45,by decide⟩).lower ∧ (cell13161 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13161 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13161 ⟨46,by decide⟩).lower ∧ (cell13161 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13161 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13161 ⟨47,by decide⟩).lower ∧ (cell13161 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13161 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13161 ⟨48,by decide⟩).lower ∧ (cell13161 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13161 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13161 ⟨49,by decide⟩).lower ∧ (cell13161 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13161 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13161 ⟨50,by decide⟩).lower ∧ (cell13161 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13161 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13161 ⟨51,by decide⟩).lower ∧ (cell13161 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13161 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13161 ⟨52,by decide⟩).lower ∧ (cell13161 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13161 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13161 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13161 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13161,cell13161,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13161 i).lower ∧
    (cell13161 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13161 i).upper ≤ (0.532 : ℝ) ∧
    (cell13161 i).centre ≤ (0.1 : ℝ) ∧ (cell13161 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13161 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13161 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13161

/-! The local source numeric instances at 13161 have no network premises. -/
namespace BstLean.Part269.N13161
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13161)
open BstLean.Part268 (cell13161)

noncomputable def sourceNumerics13161 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13161 (cell13161 i)
      scalarRow13161.M scalarRow13161.H scalarRow13161.xi := by
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
    energy_allowance := scalarRow13161.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13161]
    centre_nonneg := (scalarRow13161.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13161])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13161
/-! Actual 13162 scalar aliases and the unchanged imported parallel allowance. -/
namespace BstLean.Part269.N13162
open BstLean.Part264
open Real
theorem pilot_wn_upper : BstLean.Part153.wn 13162 ≤ (1.035169658097 : ℝ) := by
  have hr : (114.725759966975 : ℝ) ≤ √(13162 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold BstLean.Part153.wn
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + 2 / (114.725759966975 : ℝ)) ^ 2 := by gcongr
    _ ≤ _ := by norm_num
theorem pilot_finite_centre_upper : BstLean.Part211.finiteEnergy 13162 13162 (11 / 1000) ≤
    (0.008331929119 : ℝ) := by
  have h := BstLean.Part269.finite_centre_scaled (n := 13162) (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hr : (114.725759966975 : ℝ) ≤ √(13162 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  let K : ℝ := 1792 / 10000 * 1.421981 + 2 * (1792 / 10000) * 1.62763 +
    4 * (1 / 2.506628) * 1.036505 * 0.878679 *
      (81 / 1000 + (1792 / 10000) ^ 2 / 13162)
  have hdiv : K / √(13162 : ℝ) ≤ K / 114.725759966975 :=
    div_le_div_of_nonneg_left (by dsimp [K]; positivity) (by norm_num) hr
  have hnum : K / 114.725759966975 ≤ (0.008331929119 : ℝ) := by norm_num [K]
  exact h.trans (hdiv.trans hnum)
noncomputable def pilotParallelCap : ℝ := BstLean.Part269.scalarRow13162.xi
theorem pilot_gMinus_lower : (0.99886685 : ℝ) ≤ BstLean.Part211.gMinus 13162 := gMinus_lower (by norm_num)
theorem pilot_gPlus_upper : BstLean.Part211.gPlus 13162 ≤ (1.00113378 : ℝ) := gPlus_upper (by norm_num)
theorem pilot_gPlus_lower : (1 : ℝ) ≤ BstLean.Part211.gPlus 13162 := gPlus_lower 13162
end BstLean.Part269.N13162

/-! Rational bounds for the scalar constants in the Part211 centre formula. -/
namespace BstLean.Part269.N13162
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real BstLean.Part153 BstLean.Part154

theorem pilot_wn_lower : (1.035169658096 : ℝ) ≤ wn 13162 := by
  have hn : √(13162 : ℝ) ≤ 114.725759966976 := sqrt_le_iff.mpr (by norm_num)
  have hn0 : 0 < √(13162 : ℝ) := by positivity
  have hd : (2 : ℝ) / 114.725759966976 ≤ 2 / √(13162 : ℝ) := by gcongr
  unfold wn
  simp only [Nat.cast_ofNat]
  nlinarith

theorem pilot_rho_bounds : (0.000242889521 : ℝ) ≤ rhoBar 13162 BstLean.Part154.csC ∧
    rhoBar 13162 BstLean.Part154.csC ≤ 0.000242889897 := by
  have hw := pilot_wn_upper
  have hwl := pilot_wn_lower
  have hc := cs_lower
  have hcu := BstLean.Part264.pilot_cs_upper
  have hc0 : 0 < BstLean.Part154.csC := by linarith
  unfold rhoBar
  simp only [Nat.cast_ofNat]
  constructor
  · calc
      _ ≤ 4 * (1.035169658096 : ℝ) / (1.295212 * 13162) := by norm_num
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 4 * (1.035169658097 : ℝ) / (1.29521 * 13162) := by gcongr
      _ ≤ (0.000242889897 : ℝ) := by norm_num

theorem pilot_nu_upper : nuR (rhoBar 13162 BstLean.Part154.csC) ≤ 0.000971618584 := by
  have h := pilot_rho_bounds
  unfold nuR
  nlinarith

theorem pilot_piBar_upper : piBar (rhoBar 13162 BstLean.Part154.csC) ≤ (1 / 10 ^ 40 : ℝ) := by
  exact BstLean.Part264b.piBar_upper_of_bounds
    (lt_of_lt_of_le (by norm_num) pilot_rho_bounds.1)
    (pilot_rho_bounds.2.trans (by norm_num))

theorem pilot_cc_bounds : cc0 (rhoBar 13162 BstLean.Part154.csC) (piBar (rhoBar 13162 BstLean.Part154.csC)) ≤ 0.000185520634 ∧
    cc1 (rhoBar 13162 BstLean.Part154.csC) (piBar (rhoBar 13162 BstLean.Part154.csC)) ≤ 0.000118048074 ∧
    cc2 (rhoBar 13162 BstLean.Part154.csC) ≤ 0.000068527889 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hr0 : 0 ≤ rhoBar 13162 BstLean.Part154.csC := by linarith
  have hv := pilot_nu_upper
  have hv0 : 0 ≤ nuR (rhoBar 13162 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp := pilot_piBar_upper
  have hp0 : 0 ≤ piBar (rhoBar 13162 BstLean.Part154.csC) := by unfold piBar; positivity
  have hz := BstLean.Part264.pilot_phi_zero_upper
  have ho := BstLean.Part264.pilot_phi_one_upper
  have hz0 := (phiG_pos 0).le
  have ho0 := (phiG_pos 1).le
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hs1 : √(rhoBar 13162 BstLean.Part154.csC * nuR (rhoBar 13162 BstLean.Part154.csC)) ≤ 0.000485794543 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (0.000242889897 : ℝ) * 0.000971618584 := by gcongr
      _ ≤ (0.000485794543 : ℝ) ^ 2 := by norm_num
  have hs2 : √(piBar (rhoBar 13162 BstLean.Part154.csC) * nuR (rhoBar 13162 BstLean.Part154.csC)) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000971618584 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  have hs3 : √(piBar (rhoBar 13162 BstLean.Part154.csC) * rhoBar 13162 BstLean.Part154.csC) ≤ 1 / 10 ^ 20 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (1 / 10 ^ 40 : ℝ) * 0.000242889897 := by gcongr
      _ ≤ (1 / 10 ^ 20 : ℝ) ^ 2 := by norm_num
  constructor
  · unfold cc0
    calc
      _ ≤ (0.399 : ℝ) * 0.000242889897 / 2 + 0.399 * 0.000971618584 / (2 * 1.414213562) +
          (3 / 2) * 0.399 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000185520634 : ℝ) := by norm_num
  constructor
  · unfold cc1
    calc
      _ ≤ (0.243 : ℝ) * 0.000485794543 + 2 * (1 / 10 ^ 20) := by gcongr
      _ ≤ (0.000118048074 : ℝ) := by norm_num
  · unfold cc2
    calc
      _ ≤ (0.399 : ℝ) * 0.000242889897 / 1.414213562 := by gcongr
      _ ≤ (0.000068527889 : ℝ) := by norm_num

end BstLean.Part269.N13162

/-! The scalar terms in the local centre moment allowance have rational bounds. -/
namespace BstLean.Part269.N13162
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part194 BstLean.Part211

theorem pilot_qb_upper : QB (rhoBar 13162 BstLean.Part154.csC) (piBar (rhoBar 13162 BstLean.Part154.csC)) ≤ 1.48635E-7 := by
  have hr0 : 0 ≤ rhoBar 13162 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 : 0 ≤ piBar (rhoBar 13162 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13162 BstLean.Part154.csC) := by unfold nuR; positivity
  have h0 : 0 ≤ cc0 (rhoBar 13162 BstLean.Part154.csC) (piBar (rhoBar 13162 BstLean.Part154.csC)) := by unfold cc0; positivity
  have h1 : 0 ≤ cc1 (rhoBar 13162 BstLean.Part154.csC) (piBar (rhoBar 13162 BstLean.Part154.csC)) := by unfold cc1; positivity
  have h2 : 0 ≤ cc2 (rhoBar 13162 BstLean.Part154.csC) := by unfold cc2; positivity
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
    _ ≤ (0.000185520634 : ℝ) ^ 2 + 0.000118048074 ^ 2 + 3 * 0.000068527889 ^ 2 +
        2 * 0.797885 * 0.000185520634 * 0.000118048074 + 2 * 0.000185520634 * 0.000068527889 +
        4 * 0.797885 * 0.000118048074 * 0.000068527889 := by gcongr
    _ ≤ (1.48635E-7 : ℝ) := by norm_num

theorem pilot_bn_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) : bN 13162 BstLean.Part154.csC Θ ≤ 0.002533867110 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hq := pilot_qb_upper
  have hr0 : 0 ≤ rhoBar 13162 BstLean.Part154.csC := by linarith
  have hp0 : 0 ≤ piBar (rhoBar 13162 BstLean.Part154.csC) := piBar_nonneg _
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  have hv0 : 0 ≤ nuR (rhoBar 13162 BstLean.Part154.csC) := by unfold nuR; positivity
  have hq0 : 0 ≤ QB (rhoBar 13162 BstLean.Part154.csC) (piBar (rhoBar 13162 BstLean.Part154.csC)) := by
    unfold QB cc0 cc1 cc2
    positivity
  have hw0 : 0 ≤ wn 13162 := le_trans (by norm_num) pilot_wn_lower
  unfold bN
  calc
    _ ≤ 4 * Θ * 1.035169658097 * 1.48635E-7 / (0.000242889521 : ℝ) := by gcongr
    _ ≤ 0.002533867110 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_linear_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) :
    linearAllowance 13162 BstLean.Part154.csC Θ ≤ 0.002809719023 + 0.000640267105 * Θ := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hw := pilot_wn_upper
  have hv := pilot_nu_upper
  have hp := pilot_piBar_upper
  have hπ := pi_gt_d6.le
  have hr0 : 0 ≤ rhoBar 13162 BstLean.Part154.csC := by linarith
  have hv0 : 0 ≤ nuR (rhoBar 13162 BstLean.Part154.csC) := by unfold nuR; positivity
  have hp0 := piBar_nonneg (rhoBar 13162 BstLean.Part154.csC)
  unfold linearAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 4 * (1.035169658097 : ℝ) * ((2 * Θ * 0.000242889897 +
        (6863 / 10000) * 0.000242889897 * 13162 * 0.000971618584) / 3.141592 +
        Θ * (1 / 10 ^ 40)) := by gcongr
    _ ≤ 0.002809719023 + 0.000640267105 * Θ := by ring_nf; nlinarith only [hΘ]

theorem pilot_first_gap_lower : (0.09438 : ℝ) ≤ gap 2 (rhoBar 13162 BstLean.Part154.csC) 1.22 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * rhoBar 13162 BstLean.Part154.csC) :=
    le_sqrt_of_sq_le (by linarith)
  have hk : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √1.22 ≤ 0.905358 := by
    calc
      _ ≤ (1 : ℝ) / 1.1045361 := by gcongr
      _ ≤ (0.905358 : ℝ) := by norm_num
  unfold gap
  linarith

theorem pilot_gamma_bounds {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    0 < gammaRatio 13162 0.011 Θ ∧ gammaRatio 13162 0.011 Θ ≤ 0.000083499266 := by
  have hΘ : 0 < Θ := lt_of_lt_of_le (by norm_num) hw.1
  have hΘ1 := hw.2
  have hn := pilot_wn_upper
  have hn0 : 0 < wn 13162 := lt_of_lt_of_le (by norm_num) pilot_wn_lower
  unfold gammaRatio
  simp only [Nat.cast_ofNat]
  constructor
  · positivity
  · calc
      _ ≤ 2 * (1.035169658097 : ℝ) * 0.525 / ((1 - 0.011) * 13162) := by gcongr
      _ ≤ (0.000083499266 : ℝ) := by norm_num

theorem pilot_second_gap_lower {Θ : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) :
    (0.055043 : ℝ) ≤ gap 1 (gammaRatio 13162 0.011 Θ) 1.12 := by
  have hr := pilot_gamma_bounds hw
  have hs : (0.99995499 : ℝ) ≤ √(1 - gammaRatio 13162 0.011 Θ) :=
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
    badAllowance 13162 BstLean.Part154.csC 0.011 1.22 1.12 Θ ≤ 0.000316885158 := by
  have hr := pilot_rho_bounds
  have hrlo := hr.1
  have hrhi := hr.2
  have hg := pilot_gamma_bounds hw
  have hg1 := pilot_first_gap_lower
  have hg2 := pilot_second_gap_lower hw
  have ht1 : tail 2 (rhoBar 13162 BstLean.Part154.csC) 1.22 ≤ 1.1283E-8 := by
    have he : (18.3 : ℝ) ≤ gap 2 (rhoBar 13162 BstLean.Part154.csC) 1.22 ^ 2 / (2 * rhoBar 13162 BstLean.Part154.csC) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * rhoBar 13162 BstLean.Part154.csC)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_3_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have ht2 : tail 1 (gammaRatio 13162 0.011 Θ) 1.12 ≤ 1.3781E-8 := by
    have he : (18.1 : ℝ) ≤ gap 1 (gammaRatio 13162 0.011 Θ) 1.12 ^ 2 /
        (2 * gammaRatio 13162 0.011 Θ) := by
      apply (le_div_iff₀ (by linarith : 0 < 2 * gammaRatio 13162 0.011 Θ)).mpr
      nlinarith
    unfold tail
    apply le_trans ?_ BstLean.Part269.Tails.exp_minus_18_1_upper
    apply exp_le_exp.mpr
    rw [neg_div]
    linarith
  have hw' := pilot_wn_upper
  have ht10 : 0 ≤ tail 2 (rhoBar 13162 BstLean.Part154.csC) 1.22 := (exp_pos _).le
  have ht20 : 0 ≤ tail 1 (gammaRatio 13162 0.011 Θ) 1.12 := (exp_pos _).le
  have hk1 : (1.1045361 : ℝ) ≤ √1.22 := le_sqrt_of_sq_le (by norm_num)
  have hk2 : (1.05830052 : ℝ) ≤ √1.12 := le_sqrt_of_sq_le (by norm_num)
  unfold badAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1.035169658097 : ℝ) * 13162 *
        (1.1283E-8 / 1.1045361 + 1.3781E-8 / 1.05830052) := by gcongr
    _ ≤ (0.000316885158 : ℝ) := by norm_num

theorem pilot_moment_upper {Θ S : ℝ} (hw : Θ ∈ Icc (0.46 : ℝ) 0.525) (hS : 0 ≤ S) :
    momentAllowance 13162 BstLean.Part154.csC 0.011 1.22 1.12 Θ S ≤ 0.2654 * S + 0.003126604181 + 0.003174134215 * Θ := by
  have hΘ : 0 ≤ Θ := le_trans (by norm_num) hw.1
  have hr := BstLean.Part264.pilot_rest_upper hS
  have hl := pilot_linear_upper hΘ
  have hb := pilot_bn_upper hΘ
  have ht := pilot_bad_upper hw
  unfold momentAllowance
  linarith

end BstLean.Part269.N13162

/-! Bounds for the full computed-centre formula with local endpoints. -/
namespace BstLean.Part269.N13162
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_centre_qb_nonneg : 0 ≤ QB (rhoBar 13162 BstLean.Part154.csC) (piBar (rhoBar 13162 BstLean.Part154.csC)) := by
  have hr0 : 0 ≤ rhoBar 13162 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hp0 := piBar_nonneg (rhoBar 13162 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13162 BstLean.Part154.csC) := by unfold nuR; positivity
  have hφ0 := (phiG_pos 0).le
  have hφ1 := (phiG_pos 1).le
  unfold QB cc0 cc1 cc2
  positivity

theorem pilot_centre_bn_nonneg {Θ : ℝ} (hΘ : 0 ≤ Θ) : 0 ≤ bN 13162 BstLean.Part154.csC Θ := by
  have hr0 : 0 ≤ rhoBar 13162 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13162 := le_trans (by norm_num) pilot_wn_lower
  have hq0 := pilot_centre_qb_nonneg
  unfold bN
  positivity

theorem pilot_centre_moment_nonneg {Θ S : ℝ} (hΘ : 0 ≤ Θ) (hS : 0 ≤ S) :
    0 ≤ momentAllowance 13162 BstLean.Part154.csC 0.011 1.22 1.12 Θ S := by
  have hr0 : 0 ≤ rhoBar 13162 BstLean.Part154.csC := le_trans (by norm_num) pilot_rho_bounds.1
  have hw0 : 0 ≤ wn 13162 := le_trans (by norm_num) pilot_wn_lower
  have hp0 := piBar_nonneg (rhoBar 13162 BstLean.Part154.csC)
  have hv0 : 0 ≤ nuR (rhoBar 13162 BstLean.Part154.csC) := by unfold nuR; positivity
  have hk0 : 0 ≤ K0 := by
    unfold K0
    exact div_nonneg (by linarith [pi_gt_three]) (by positivity)
  have hb0 := pilot_centre_bn_nonneg hΘ
  have hrest : 0 ≤ restAllowance BstLean.Part154.csC 0.011 1.22 1.12 S := by unfold restAllowance; positivity
  have hlinear : 0 ≤ linearAllowance 13162 BstLean.Part154.csC Θ := by unfold linearAllowance; positivity
  have hbad : 0 ≤ badAllowance 13162 BstLean.Part154.csC 0.011 1.22 1.12 Θ := by
    unfold badAllowance BstLean.Part194.tail
    positivity
  unfold momentAllowance
  positivity

theorem pilot_deviation_upper {Θ : ℝ} (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    sharpDeviation 13162 BstLean.Part154.csC 0.011 0.46 Θ ≤ 0.051545058417 := by
  have hs : √(24 : ℝ) ≤ 4.89898 := sqrt_le_iff.mpr (by norm_num)
  have hc := cs_lower
  have hw := pilot_wn_upper
  have h1 : √(2 * (1 + (0.011 : ℝ) - BstLean.Part154.csC * 0.46 / 2) / 13162) ≤ 0.010409498106 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have h2 : √(wn 13162 * Θ) ≤ 0.737676 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have h := mul_le_mul hw hΘ1 hΘ (by norm_num : (0 : ℝ) ≤ 1.035169658097)
    linarith
  unfold sharpDeviation
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (4.89898 : ℝ) * (0.010409498106 + 2 * 0.737676 / 13162) := by gcongr
    _ ≤ (0.051545058417 : ℝ) := by norm_num

theorem pilot_n22_upper : N22bar 13162 12 ≤ 0.0015 := by
  exact BstLean.Part269.S32.uniform_n22_upper (by norm_num)

end BstLean.Part269.N13162

/-! The local centre windows fit the original parallel-centre allowance. -/
namespace BstLean.Part269.N13162
open BstLean.Part253 BstLean.Part264
open BstLean.Part264
open Real Set BstLean.Part153 BstLean.Part154 BstLean.Part211

theorem pilot_plow_lower : (0.560523727936 : ℝ) ≤ plow 13162 (0.011) := by
  have hs : (0.5610779 : ℝ) ≤ √((1 - 0.011) / π) := by
    apply le_sqrt_of_sq_le
    apply (le_div_iff₀ pi_pos).mpr
    linarith [pi_lt_d6]
  unfold plow
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.5610779 : ℝ) * (1 - 13 / 13162) := by norm_num
    _ ≤ _ := by gcongr

theorem pilot_emp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052299624644)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330280233) : eMP 13162 0.011 xi bn ≤ 0.001145850427 := by
  have hp := pi_lt_d6.le
  have hs : √(π * bn / ((13162 : ℝ) * (1 - 0.011))) ≤ 0.000566614182 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    calc
      _ ≤ (3.141593 : ℝ) * 0.001330280233 / (13162 * (1 - 0.011)) := by gcongr
      _ ≤ (0.000566614182 : ℝ) ^ 2 := by norm_num
  unfold eMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ 2 * (0.000566614182 : ℝ) + 3.141593 * 0.052299624644 / (13162 * (1 - 0.011)) := by gcongr
    _ ≤ (0.001145850427 : ℝ) := by norm_num

theorem pilot_pibar_mp_upper {xi bn : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052299624644)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330280233) : PiBarMP 13162 12 0.011 xi bn ≤ 0.158367780618 := by
  have he := pilot_emp_upper hxi hxi1 hbn hbn1
  have he0 : 0 ≤ eMP 13162 0.011 xi bn := by unfold eMP; positivity
  have hsbn : √bn ≤ 0.036473006910 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hp : √π ≤ 1.772454 := sqrt_le_iff.mpr ⟨by norm_num, by linarith [pi_lt_d6]⟩
  have hn : (114.093023450165 : ℝ) ≤ √((13162 : ℝ) * (1 - 0.011)) := le_sqrt_of_sq_le (by norm_num)
  have hn' : (114.725759966975 : ℝ) ≤ √(13162 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hs : √((16 : ℝ) * 12 * (1 + 0.011) / 13162) ≤ 0.121440976001 :=
    sqrt_le_iff.mpr (by norm_num)
  unfold PiBarMP
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.036473006910 + 0.052299624644 * 1.772454 / (2 * (114.093023450165 : ℝ))) * (1 + 0.001145850427) +
        8 / (13162 * 114.725759966975) + 0.121440976001 := by gcongr
    _ ≤ (0.158367780618 : ℝ) := by norm_num

theorem pilot_parallel_oracle_upper {xi bn cd : ℝ} (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052299624644)
    (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330280233) (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280236170278) :
    parallelOracle 13162 0.011 xi bn cd ≤ 0.159323459058 := by
  have hp := pilot_pibar_mp_upper hxi hxi1 hbn hbn1
  have hp0 : 0 ≤ PiBarMP 13162 12 0.011 xi bn := by
    have he0 : 0 ≤ eMP 13162 0.011 xi bn := by unfold eMP; positivity
    unfold PiBarMP
    positivity
  have hpl : (0.560523727936 : ℝ) ≤ plow 13162 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.725759966975 : ℝ) ≤ √(13162 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  unfold parallelOracle
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (1 + (0.280236170278 : ℝ) / (2 * 0.560523727936 * 114.725759966975)) * 0.158367780618 +
        0.280236170278 ^ 2 / (2 * 0.560523727936 * 114.725759966975) := by gcongr
    _ ≤ (0.159323459058 : ℝ) := by norm_num

theorem pilot_parallel_formula_bound {xi bn cd Θ : ℝ}
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 0.052299624644) (hbn : 0 ≤ bn) (hbn1 : bn ≤ 0.001330280233)
    (hcd : 0 ≤ cd) (hcd1 : cd ≤ 0.280236170278) (hΘ : 0 ≤ Θ) (hΘ1 : Θ ≤ 0.525) :
    parallelFormula 13162 13162 0.011 xi bn cd Θ 1.22 ≤ pilotParallelCap := by
  have ho := pilot_parallel_oracle_upper hxi hxi1 hbn hbn1 hcd hcd1
  have hp : (0.560523727936 : ℝ) ≤ plow 13162 (11 / 1000) := by
    convert pilot_plow_lower using 1 <;> norm_num
  have hn : (114.725759966975 : ℝ) ≤ √(13162 : ℝ) := le_sqrt_of_sq_le (by norm_num)
  have hNr := pilot_n22_upper
  have hNr0 : 0 ≤ N22bar 13162 12 := by unfold N22bar N12bar; positivity
  have hs : √((1.22 : ℝ) * Θ) ≤ 0.800313 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hr : xiNr 13162 Θ 1.22 ≤ 0.011558873094 := by
    unfold xiNr
    simp only [Nat.cast_ofNat]
    calc
      _ ≤ ((0.525 : ℝ) * 1.0015 + 0.800313) / 114.725759966975 := by gcongr <;> linarith
      _ ≤ (0.011558873094 : ℝ) := by norm_num
  have hr0 : 0 ≤ xiNr 13162 Θ 1.22 := by unfold xiNr; positivity
  have hf : finiteEnergy 13162 13162 0.011 ≤ 0.008331929119 := by
    convert pilot_finite_centre_upper using 1 <;> norm_num
  have hf0 := finiteEnergy_nonneg 13162 13162 (by norm_num : (0 : ℝ) ≤ 0.011)
  have hp0 : 0 ≤ plow 13162 (11 / 1000) := le_trans (by norm_num) hp
  have he0 : 0 ≤ eMP 13162 0.011 xi bn := by unfold eMP; positivity
  have hpi0 : 0 ≤ PiBarMP 13162 12 0.011 xi bn := by unfold PiBarMP; positivity
  have ho0 : 0 ≤ parallelOracle 13162 0.011 xi bn cd := by unfold parallelOracle; positivity
  unfold parallelFormula BstLean.Part206.parallelAllowance
  simp only [Nat.cast_ofNat]
  calc
    _ ≤ (0.159323459058 + 0.011558873094 + (0.008331929119 : ℝ) *
        (1 + 2 * (0.280236170278 + 0.011558873094) / (0.560523727936 * 114.725759966975))) ^ 2 := by gcongr
    _ ≤ pilotParallelCap := by norm_num [pilotParallelCap, BstLean.Part269.scalarRow13162]

end BstLean.Part269.N13162

/-! The original eight local profiles supply actual 13162 moment certificates. -/
namespace BstLean.Part269.N13162
open BstLean.Part264
open Real Set
open BstLean.Part153 BstLean.Part154 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile)

noncomputable def pilot_groupMomentCertificate {g : Fin 10} (hg : NeededGroup g) :
    MomentCertificate 13162 0.011 1.22 1.12 0.46 (groupTheta g) (groupProfile g)
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
    0 ≤ momentAllowance 13162 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ∧
    momentAllowance 13162 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤ 0.052299624644 ∧
    0 ≤ bN 13162 BstLean.Part154.csC (groupTheta g) ∧ bN 13162 BstLean.Part154.csC (groupTheta g) ≤ 0.001330280233 := by
  have G := BstLean.Part253.group_scalar hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hm := pilot_moment_upper G.window G.profile_nonneg
  have hb := pilot_bn_upper hΘ
  exact ⟨pilot_centre_moment_nonneg hΘ G.profile_nonneg,
    by have := G.profile_le; have := G.window.2; linarith,
    pilot_centre_bn_nonneg hΘ, by have := G.window.2; linarith⟩

theorem pilot_group_parallel {g : Fin 10} (hg : NeededGroup g) :
    parallelFormula 13162 13162 0.011
      (momentAllowance 13162 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13162 BstLean.Part154.csC (groupTheta g))
      (√(momentAllowance 13162 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g)) +
        sharpDeviation 13162 BstLean.Part154.csC 0.011 0.46 (groupTheta g)) (groupTheta g) 1.22 ≤ pilotParallelCap := by
  have G := BstLean.Part253.group_scalar hg
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  have hΘ : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have hd0 : 0 ≤ sharpDeviation 13162 BstLean.Part154.csC 0.011 0.46 (groupTheta g) := by
    unfold sharpDeviation
    positivity
  have hxs : √(momentAllowance 13162 BstLean.Part154.csC 0.011 1.22 1.12
      (groupTheta g) (groupProfile g)) ≤ 0.228691111861 :=
    sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hd := pilot_deviation_upper hΘ G.window.2
  exact pilot_parallel_formula_bound hxi0 hxi1 hbn0 hbn1 (by positivity) (by linarith)
    hΘ G.window.2

theorem pilot_group_relative_gap {g : Fin 10} (hg : NeededGroup g) :
    eMP 13162 0.011
      (momentAllowance 13162 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g))
      (bN 13162 BstLean.Part154.csC (groupTheta g)) ≤ 1 / 10 := by
  obtain ⟨hxi0,hxi1,hbn0,hbn1⟩ := pilot_group_moment_bounds hg
  exact (pilot_emp_upper hxi0 hxi1 hbn0 hbn1).trans (by norm_num)

end BstLean.Part269.N13162
/-! The actual computed-centre upper energy formula at 13162. -/
namespace BstLean.Part269.N13162
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
end BstLean.Part269.N13162

/-! Local full-centre bounds at the original imported allowances. -/
namespace BstLean.Part269.N13162
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13162)
open BstLean.Part268 (cell13162)
noncomputable def pilotGroupCentre (g : Fin 10) : ℝ :=
  match g.val with
  | 1 => 0.084245993380
  | 2 => 0.085169417373
  | 3 => 0.086088282679
  | 4 => 0.087003371801
  | 5 => 0.087915649103
  | 6 => 0.088826289987
  | 7 => 0.089736713237
  | 8 => 0.090648616635
  | _ => 0

theorem pilot_group_full {g : Fin 10} (hg : NeededGroup g) :
    fullFormula 13162 13162 0.011 1.22 1.12 0.46 (groupTheta g)
      (groupProfile g) 1.22 ≤ pilotGroupCentre g := by
  have G := BstLean.Part253.group_scalar hg
  have hTheta : 0 ≤ groupTheta g := le_trans (by norm_num) G.window.1
  have HM := pilot_moment_upper G.window G.profile_nonneg
  have HM0 : momentAllowance 13162 BstLean.Part154.csC 0.011 1.22 1.12 (groupTheta g) (groupProfile g) ≤
      0.2654 * groupProfile g + 0.003129300233 + 0.003177129197 * groupTheta g := by
    nlinarith only [HM,hTheta]
  apply (BstLean.Part269.S32.uniform_group_full (by norm_num) hg HM0).trans
  match g with
  | ⟨0,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hl; omega)
  | ⟨1,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨2,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨3,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨4,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨5,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨6,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨7,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨8,h⟩ => norm_num [BstLean.Part269.S32.minimumGroupCentre,pilotGroupCentre]
  | ⟨9,h⟩ => exact False.elim (by rcases hg with ⟨hl,hu⟩; dsimp at hu; omega)
  | ⟨j+10,h⟩ => exact False.elim (by omega)

end BstLean.Part269.N13162

/-! Actual upper energy certificates on all 43 source endpoints at 13162. -/
namespace BstLean.Part269.N13162
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part269 (scalarRow13162)
open BstLean.Part268 (cell13162)
theorem pilot_upper_energy {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    energyRatio 13162 (gMinus 13162) (1 - (cell13162 i).lower) ≤ 1 ∧
    energyUpper 13162 (gMinus 13162) (BstLean.Part211.gPlus 13162)
      (finiteEnergy 13162 13162 0.011) (1 - (cell13162 i).lower) ≤
      (cell13162 i).energy := by
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
      have E := BstLean.Part269.S32.uniformEnergy10 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨10,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨11,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy11 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨11,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨12,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy12 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨12,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨13,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy13 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨13,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨14,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy14 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨14,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨15,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy15 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨15,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨16,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy16 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨16,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨17,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy17 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨17,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨18,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy18 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨18,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨19,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy19 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨19,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨20,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy20 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨20,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨21,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy21 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨21,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨22,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy22 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨22,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨23,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy23 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨23,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨24,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy24 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨24,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨25,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy25 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨25,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨26,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy26 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨26,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨27,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy27 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨27,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨28,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy28 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨28,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨29,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy29 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨29,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨30,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy30 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨30,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨31,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy31 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨31,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨32,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy32 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨32,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨33,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy33 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨33,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨34,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy34 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨34,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨35,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy35 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨35,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨36,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy36 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨36,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨37,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy37 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨37,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨38,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy38 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨38,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨39,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy39 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨39,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨40,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy40 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨40,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨41,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy41 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨41,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨42,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy42 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨42,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨43,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy43 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨43,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨44,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy44 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨44,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨45,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy45 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨45,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨46,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy46 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨46,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨47,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy47 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨47,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨48,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy48 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨48,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨49,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy49 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨49,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨50,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy50 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨50,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨51,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy51 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨51,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨52,h⟩ =>
      have E := BstLean.Part269.S32.uniformEnergy52 (n := 13162) (by norm_num)
        (q := 1 - (cell13162 ⟨52,by decide⟩).lower)
        (by norm_num [cell13162]) (by norm_num [cell13162])
      exact ⟨E.1,E.2.trans (by norm_num [cell13162])⟩
  | ⟨i+53,h⟩ => exact False.elim (by rcases hi with ⟨hl,hu⟩; dsimp at hu; omega)

end BstLean.Part269.N13162

/-! Source-cell containment and simple scalar guards at 13162. -/
namespace BstLean.Part269.N13162
open BstLean.Part264
open Real Set BstLean.Part130 BstLean.Part182 BstLean.Part211 BstLean.Part206
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13162)
open BstLean.Part268 (cell13162)
theorem pilot_sourceCell10 :
    (0.46 : ℝ) ≤ (cell13162 ⟨10,by decide⟩).lower ∧ (cell13162 ⟨10,by decide⟩).upper ≤ groupTheta (centreGroup ⟨10,by decide⟩) ∧
    (cell13162 ⟨10,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨10,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨10,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨10,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨10,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨10,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell11 :
    (0.46 : ℝ) ≤ (cell13162 ⟨11,by decide⟩).lower ∧ (cell13162 ⟨11,by decide⟩).upper ≤ groupTheta (centreGroup ⟨11,by decide⟩) ∧
    (cell13162 ⟨11,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨11,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨11,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨11,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨11,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨11,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell12 :
    (0.46 : ℝ) ≤ (cell13162 ⟨12,by decide⟩).lower ∧ (cell13162 ⟨12,by decide⟩).upper ≤ groupTheta (centreGroup ⟨12,by decide⟩) ∧
    (cell13162 ⟨12,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨12,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨12,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨12,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨12,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨12,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell13 :
    (0.46 : ℝ) ≤ (cell13162 ⟨13,by decide⟩).lower ∧ (cell13162 ⟨13,by decide⟩).upper ≤ groupTheta (centreGroup ⟨13,by decide⟩) ∧
    (cell13162 ⟨13,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨13,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨13,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨13,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨13,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨13,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell14 :
    (0.46 : ℝ) ≤ (cell13162 ⟨14,by decide⟩).lower ∧ (cell13162 ⟨14,by decide⟩).upper ≤ groupTheta (centreGroup ⟨14,by decide⟩) ∧
    (cell13162 ⟨14,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨14,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨14,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨14,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨14,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨14,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell15 :
    (0.46 : ℝ) ≤ (cell13162 ⟨15,by decide⟩).lower ∧ (cell13162 ⟨15,by decide⟩).upper ≤ groupTheta (centreGroup ⟨15,by decide⟩) ∧
    (cell13162 ⟨15,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨15,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨15,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨15,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨15,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨15,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell16 :
    (0.46 : ℝ) ≤ (cell13162 ⟨16,by decide⟩).lower ∧ (cell13162 ⟨16,by decide⟩).upper ≤ groupTheta (centreGroup ⟨16,by decide⟩) ∧
    (cell13162 ⟨16,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨16,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨16,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨16,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨16,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨16,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell17 :
    (0.46 : ℝ) ≤ (cell13162 ⟨17,by decide⟩).lower ∧ (cell13162 ⟨17,by decide⟩).upper ≤ groupTheta (centreGroup ⟨17,by decide⟩) ∧
    (cell13162 ⟨17,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨17,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨17,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨17,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨17,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨17,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell18 :
    (0.46 : ℝ) ≤ (cell13162 ⟨18,by decide⟩).lower ∧ (cell13162 ⟨18,by decide⟩).upper ≤ groupTheta (centreGroup ⟨18,by decide⟩) ∧
    (cell13162 ⟨18,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨18,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨18,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨18,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨18,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨18,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell19 :
    (0.46 : ℝ) ≤ (cell13162 ⟨19,by decide⟩).lower ∧ (cell13162 ⟨19,by decide⟩).upper ≤ groupTheta (centreGroup ⟨19,by decide⟩) ∧
    (cell13162 ⟨19,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨19,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨19,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨19,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨19,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨19,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell20 :
    (0.46 : ℝ) ≤ (cell13162 ⟨20,by decide⟩).lower ∧ (cell13162 ⟨20,by decide⟩).upper ≤ groupTheta (centreGroup ⟨20,by decide⟩) ∧
    (cell13162 ⟨20,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨20,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨20,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨20,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨20,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨20,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell21 :
    (0.46 : ℝ) ≤ (cell13162 ⟨21,by decide⟩).lower ∧ (cell13162 ⟨21,by decide⟩).upper ≤ groupTheta (centreGroup ⟨21,by decide⟩) ∧
    (cell13162 ⟨21,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨21,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨21,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨21,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨21,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨21,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell22 :
    (0.46 : ℝ) ≤ (cell13162 ⟨22,by decide⟩).lower ∧ (cell13162 ⟨22,by decide⟩).upper ≤ groupTheta (centreGroup ⟨22,by decide⟩) ∧
    (cell13162 ⟨22,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨22,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨22,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨22,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨22,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨22,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell23 :
    (0.46 : ℝ) ≤ (cell13162 ⟨23,by decide⟩).lower ∧ (cell13162 ⟨23,by decide⟩).upper ≤ groupTheta (centreGroup ⟨23,by decide⟩) ∧
    (cell13162 ⟨23,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨23,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨23,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨23,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨23,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨23,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell24 :
    (0.46 : ℝ) ≤ (cell13162 ⟨24,by decide⟩).lower ∧ (cell13162 ⟨24,by decide⟩).upper ≤ groupTheta (centreGroup ⟨24,by decide⟩) ∧
    (cell13162 ⟨24,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨24,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨24,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨24,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨24,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨24,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell25 :
    (0.46 : ℝ) ≤ (cell13162 ⟨25,by decide⟩).lower ∧ (cell13162 ⟨25,by decide⟩).upper ≤ groupTheta (centreGroup ⟨25,by decide⟩) ∧
    (cell13162 ⟨25,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨25,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨25,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨25,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨25,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨25,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell26 :
    (0.46 : ℝ) ≤ (cell13162 ⟨26,by decide⟩).lower ∧ (cell13162 ⟨26,by decide⟩).upper ≤ groupTheta (centreGroup ⟨26,by decide⟩) ∧
    (cell13162 ⟨26,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨26,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨26,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨26,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨26,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨26,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell27 :
    (0.46 : ℝ) ≤ (cell13162 ⟨27,by decide⟩).lower ∧ (cell13162 ⟨27,by decide⟩).upper ≤ groupTheta (centreGroup ⟨27,by decide⟩) ∧
    (cell13162 ⟨27,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨27,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨27,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨27,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨27,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨27,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell28 :
    (0.46 : ℝ) ≤ (cell13162 ⟨28,by decide⟩).lower ∧ (cell13162 ⟨28,by decide⟩).upper ≤ groupTheta (centreGroup ⟨28,by decide⟩) ∧
    (cell13162 ⟨28,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨28,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨28,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨28,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨28,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨28,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell29 :
    (0.46 : ℝ) ≤ (cell13162 ⟨29,by decide⟩).lower ∧ (cell13162 ⟨29,by decide⟩).upper ≤ groupTheta (centreGroup ⟨29,by decide⟩) ∧
    (cell13162 ⟨29,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨29,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨29,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨29,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨29,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨29,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell30 :
    (0.46 : ℝ) ≤ (cell13162 ⟨30,by decide⟩).lower ∧ (cell13162 ⟨30,by decide⟩).upper ≤ groupTheta (centreGroup ⟨30,by decide⟩) ∧
    (cell13162 ⟨30,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨30,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨30,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨30,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨30,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨30,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell31 :
    (0.46 : ℝ) ≤ (cell13162 ⟨31,by decide⟩).lower ∧ (cell13162 ⟨31,by decide⟩).upper ≤ groupTheta (centreGroup ⟨31,by decide⟩) ∧
    (cell13162 ⟨31,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨31,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨31,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨31,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨31,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨31,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell32 :
    (0.46 : ℝ) ≤ (cell13162 ⟨32,by decide⟩).lower ∧ (cell13162 ⟨32,by decide⟩).upper ≤ groupTheta (centreGroup ⟨32,by decide⟩) ∧
    (cell13162 ⟨32,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨32,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨32,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨32,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨32,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨32,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell33 :
    (0.46 : ℝ) ≤ (cell13162 ⟨33,by decide⟩).lower ∧ (cell13162 ⟨33,by decide⟩).upper ≤ groupTheta (centreGroup ⟨33,by decide⟩) ∧
    (cell13162 ⟨33,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨33,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨33,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨33,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨33,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨33,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell34 :
    (0.46 : ℝ) ≤ (cell13162 ⟨34,by decide⟩).lower ∧ (cell13162 ⟨34,by decide⟩).upper ≤ groupTheta (centreGroup ⟨34,by decide⟩) ∧
    (cell13162 ⟨34,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨34,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨34,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨34,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨34,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨34,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell35 :
    (0.46 : ℝ) ≤ (cell13162 ⟨35,by decide⟩).lower ∧ (cell13162 ⟨35,by decide⟩).upper ≤ groupTheta (centreGroup ⟨35,by decide⟩) ∧
    (cell13162 ⟨35,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨35,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨35,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨35,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨35,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨35,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell36 :
    (0.46 : ℝ) ≤ (cell13162 ⟨36,by decide⟩).lower ∧ (cell13162 ⟨36,by decide⟩).upper ≤ groupTheta (centreGroup ⟨36,by decide⟩) ∧
    (cell13162 ⟨36,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨36,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨36,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨36,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨36,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨36,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell37 :
    (0.46 : ℝ) ≤ (cell13162 ⟨37,by decide⟩).lower ∧ (cell13162 ⟨37,by decide⟩).upper ≤ groupTheta (centreGroup ⟨37,by decide⟩) ∧
    (cell13162 ⟨37,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨37,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨37,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨37,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨37,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨37,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell38 :
    (0.46 : ℝ) ≤ (cell13162 ⟨38,by decide⟩).lower ∧ (cell13162 ⟨38,by decide⟩).upper ≤ groupTheta (centreGroup ⟨38,by decide⟩) ∧
    (cell13162 ⟨38,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨38,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨38,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨38,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨38,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨38,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell39 :
    (0.46 : ℝ) ≤ (cell13162 ⟨39,by decide⟩).lower ∧ (cell13162 ⟨39,by decide⟩).upper ≤ groupTheta (centreGroup ⟨39,by decide⟩) ∧
    (cell13162 ⟨39,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨39,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨39,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨39,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨39,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨39,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell40 :
    (0.46 : ℝ) ≤ (cell13162 ⟨40,by decide⟩).lower ∧ (cell13162 ⟨40,by decide⟩).upper ≤ groupTheta (centreGroup ⟨40,by decide⟩) ∧
    (cell13162 ⟨40,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨40,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨40,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨40,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨40,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨40,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell41 :
    (0.46 : ℝ) ≤ (cell13162 ⟨41,by decide⟩).lower ∧ (cell13162 ⟨41,by decide⟩).upper ≤ groupTheta (centreGroup ⟨41,by decide⟩) ∧
    (cell13162 ⟨41,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨41,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨41,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨41,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨41,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨41,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell42 :
    (0.46 : ℝ) ≤ (cell13162 ⟨42,by decide⟩).lower ∧ (cell13162 ⟨42,by decide⟩).upper ≤ groupTheta (centreGroup ⟨42,by decide⟩) ∧
    (cell13162 ⟨42,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨42,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨42,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨42,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨42,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨42,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell43 :
    (0.46 : ℝ) ≤ (cell13162 ⟨43,by decide⟩).lower ∧ (cell13162 ⟨43,by decide⟩).upper ≤ groupTheta (centreGroup ⟨43,by decide⟩) ∧
    (cell13162 ⟨43,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨43,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨43,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨43,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨43,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨43,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell44 :
    (0.46 : ℝ) ≤ (cell13162 ⟨44,by decide⟩).lower ∧ (cell13162 ⟨44,by decide⟩).upper ≤ groupTheta (centreGroup ⟨44,by decide⟩) ∧
    (cell13162 ⟨44,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨44,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨44,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨44,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨44,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨44,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell45 :
    (0.46 : ℝ) ≤ (cell13162 ⟨45,by decide⟩).lower ∧ (cell13162 ⟨45,by decide⟩).upper ≤ groupTheta (centreGroup ⟨45,by decide⟩) ∧
    (cell13162 ⟨45,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨45,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨45,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨45,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨45,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨45,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell46 :
    (0.46 : ℝ) ≤ (cell13162 ⟨46,by decide⟩).lower ∧ (cell13162 ⟨46,by decide⟩).upper ≤ groupTheta (centreGroup ⟨46,by decide⟩) ∧
    (cell13162 ⟨46,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨46,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨46,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨46,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨46,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨46,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell47 :
    (0.46 : ℝ) ≤ (cell13162 ⟨47,by decide⟩).lower ∧ (cell13162 ⟨47,by decide⟩).upper ≤ groupTheta (centreGroup ⟨47,by decide⟩) ∧
    (cell13162 ⟨47,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨47,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨47,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨47,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨47,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨47,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell48 :
    (0.46 : ℝ) ≤ (cell13162 ⟨48,by decide⟩).lower ∧ (cell13162 ⟨48,by decide⟩).upper ≤ groupTheta (centreGroup ⟨48,by decide⟩) ∧
    (cell13162 ⟨48,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨48,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨48,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨48,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨48,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨48,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell49 :
    (0.46 : ℝ) ≤ (cell13162 ⟨49,by decide⟩).lower ∧ (cell13162 ⟨49,by decide⟩).upper ≤ groupTheta (centreGroup ⟨49,by decide⟩) ∧
    (cell13162 ⟨49,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨49,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨49,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨49,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨49,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨49,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell50 :
    (0.46 : ℝ) ≤ (cell13162 ⟨50,by decide⟩).lower ∧ (cell13162 ⟨50,by decide⟩).upper ≤ groupTheta (centreGroup ⟨50,by decide⟩) ∧
    (cell13162 ⟨50,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨50,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨50,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨50,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨50,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨50,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell51 :
    (0.46 : ℝ) ≤ (cell13162 ⟨51,by decide⟩).lower ∧ (cell13162 ⟨51,by decide⟩).upper ≤ groupTheta (centreGroup ⟨51,by decide⟩) ∧
    (cell13162 ⟨51,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨51,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨51,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨51,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨51,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨51,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_sourceCell52 :
    (0.46 : ℝ) ≤ (cell13162 ⟨52,by decide⟩).lower ∧ (cell13162 ⟨52,by decide⟩).upper ≤ groupTheta (centreGroup ⟨52,by decide⟩) ∧
    (cell13162 ⟨52,by decide⟩).upper ≤ (0.532 : ℝ) ∧ (cell13162 ⟨52,by decide⟩).centre ≤ (0.1 : ℝ) ∧ (cell13162 ⟨52,by decide⟩).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 ⟨52,by decide⟩).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 ⟨52,by decide⟩).centre = pilotGroupCentre (centreGroup ⟨52,by decide⟩) := by
  norm_num [scalarRow13162,cell13162,groupTheta,centreGroup,pilotGroupCentre]

theorem pilot_source_cell {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    (0.46 : ℝ) ≤ (cell13162 i).lower ∧
    (cell13162 i).upper ≤ groupTheta (centreGroup i) ∧
    (cell13162 i).upper ≤ (0.532 : ℝ) ∧
    (cell13162 i).centre ≤ (0.1 : ℝ) ∧ (cell13162 i).energy ≤ (1 : ℝ) ∧
    (1 - (cell13162 i).lower) ∈ Icc (-1 : ℝ) 1 ∧
    (cell13162 i).centre = pilotGroupCentre (centreGroup i) := by
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

end BstLean.Part269.N13162

/-! The local source numeric instances at 13162 have no network premises. -/
namespace BstLean.Part269.N13162
open BstLean.Part264
open Real Set
open BstLean.Part130 BstLean.Part211
open BstLean.Part253 (NeededGroup groupTheta groupProfile centreGroup)
open BstLean.Part269 (scalarRow13162)
open BstLean.Part268 (cell13162)

noncomputable def sourceNumerics13162 {i : Fin 60} (hi : 10 ≤ i.val ∧ i.val ≤ 52) :
    BstLean.Part269.CellSourceNumerics 13162 (cell13162 i)
      scalarRow13162.M scalarRow13162.H scalarRow13162.xi := by
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
    energy_allowance := scalarRow13162.energy_allowance
    parallel_nonneg := by norm_num [scalarRow13162]
    centre_nonneg := (scalarRow13162.certificate i).centre_nonneg
    centre_upper := hc
    direction := by
      intro c τ e xi eta δ hw he hxi hxi1 hop
      exact (BstLean.Part269.D32.direction_budget_le (by norm_num)
        c τ e xi eta δ hw he hxi hxi1 hop).trans (by norm_num [scalarRow13162])
    source_lower := hl
    source_upper := hu
    source_upper532 := hu532
    full_scalar := by rw [hcentre]; exact pilot_group_full hg
    parallel_scalar := pilot_group_parallel hg
    upper_scalar := E.2 }

end BstLean.Part269.N13162